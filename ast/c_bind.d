module ast.c_bind;

// Optimized for GL.h and SDL.h; may not work for others!! 
import ast.base, ast.modules, ast.structure, ast.casting, ast.static_arrays, ast.tuples: AstTuple = Tuple;

import tools.compat, tools.functional;
alias asmfile.startsWith startsWith;

extern(C) {
  int pipe(int*);
  int close(int);
}

string buf;
string readStream(InputStream IS) {
  if (!buf) buf = new char[1024*1024];
  int reslen;
  ubyte[1024] buffer;
  int i;
  do {
    i = IS.read(buffer);
    if (i < 0) throw new Exception(Format("Read error: ", i));
    if (buf.length < reslen + i)
      buf.length = cast(int) (buf.length * 1.5);
    buf[reslen .. reslen + i] = cast(string) buffer[0 .. i];
    reslen += i;
  } while (i);
  return buf[0 .. reslen].dup;
}

string readback(string cmd) {
  // logln("> ", cmd);
  int[2] fd; // read end, write end
  if (-1 == pipe(fd.ptr)) throw new Exception(Format("Can't open pipe! "));
  scope(exit) close(fd[0]);
  auto cmdstr = Format(cmd, " >&", fd[1], " &");
  system(toStringz(cmdstr));
  close(fd[1]);
  scope fs = new CFile(fdopen(fd[0], "r"), FileMode.In);
  return readStream(fs);
}

import
  ast.aliasing, ast.pointer, ast.fun, ast.namespace, ast.int_literal,
  ast.fold, ast.opers;
import tools.time;
void parseHeader(string filename, string src, ParseCb rest) {
  auto start_time = sec();
  string newsrc;
  bool inEnum;
  string[] buffer;
  void flushBuffer() { foreach (def; buffer) newsrc ~= def ~ ";"; buffer = null; }
  foreach (line; src.split("\n")) {
    // special handling for fenv.h; shuffle #defines past the enum
    if (line.startsWith("enum")) inEnum = true;
    if (line.startsWith("}")) { inEnum = false; newsrc ~= line; flushBuffer; continue; }
    if (line.startsWith("#define")) { if (inEnum) buffer ~= line; else {  newsrc ~= line; newsrc ~= ";"; } }
    if (line.startsWith("#")) continue;
    newsrc ~= line ~ " ";
  }
  // no need to remove comments; the preprocessor already did that
  auto statements = newsrc.split(";") /map/ &strip;
  // mini parser
  Named[] res;
  Named[string] cache;
  auto myNS = new MiniNamespace("parse_header");
  myNS.sup = namespace();
  myNS.internalMode = true;
  namespace.set(myNS);
  scope(exit) namespace.set(myNS.sup);
  void add(string name, Named n) {
    if (myNS.lookup(name)) { return; } // duplicate definition. meh.
    auto ea = cast(ExprAlias) n;
    if (ea) {
      if (!gotImplicitCast(ea.base, (IType it) { return !cast(AstTuple) it; })) {
        logln("Weird thing ", ea);
        asm { int 3; }
      }
    }
    // logln("add ", name, " <- ", n);
    myNS._add(name, cast(Object) n);
    res ~= n;
    cache[name] = n;
  }
  
  IType matchSimpleType(ref string text) {
    bool accept(string s) {
      auto t2 = text;
      while (s.length) {
        string part1, part2;
        if (!s.gotIdentifier(part1)) return false;
        if (!t2.gotIdentifier(part2)) return false;
        if (part1 != part2) return false;
        s = s.strip();
      }
      text = t2;
      return true;
    }
    if (auto rest = text.strip().startsWith("...")) { text = rest; return Single!(Variadic); }
    if (accept("unsigned long int"))  return Single!(SysInt);
    if (accept("unsigned long long int") || accept("unsigned long long"))
      return Single!(Long);
    if (accept("long long int") || accept("long long"))
      return Single!(Long);
    if (accept("unsigned int") || accept("signed int") || accept("long int") || accept("int")) return Single!(SysInt);
    if (accept("unsigned char") || accept("signed char") || accept("char")) return Single!(Char);
    if (accept("signed short int") || accept("unsigned short int") || accept("unsigned short") || accept("short int") || accept("short")) return Single!(Short);
    if (accept("void")) return Single!(Void);
    if (accept("float")) return Single!(Float);
    // TODO: work out packing for double
    if (accept("double")) return Single!(Double);
    if (accept("struct")) {
      string name;
      text.gotIdentifier(name);
      if (auto p = name in cache) return cast(IType) *p;
      else return Single!(Void);
    }
    string id;
    if (!text.gotIdentifier(id)) return null;
    if (auto p = id in cache) return cast(IType) *p;
    return null;
  }
  IType matchType(ref string text) {
    text.accept("const");
    text.accept("__const");
    if (auto ty = matchSimpleType(text)) {
      while (text.accept("*")) ty = new Pointer(ty);
      return ty;
    } else return null;
  }
  IType matchParam(ref string text) {
    IType ty = matchType(text);
    if (!ty) return null;
    text.accept("__restrict");
    text.accept("__const");
    string id;
    gotIdentifier(text, id);
    if (auto sa = cast(StaticArray) resolveType(ty)) {
      ty = new Pointer(sa.elemType);
    }
    redo:if (text.startsWith("[")) {
      ty = new Pointer(ty);
      text.slice("]");
      goto redo;
    }
    text.accept(",");
    return ty;
  }
  while (statements.length) {
    auto stmt = statements.take(), start = stmt;
    // logln("> ", stmt.replace("\n", "\\"));
    stmt.accept("__extension__");
    if (stmt.accept("#define")) {
      if (stmt.accept("__")) continue; // internal
      string id;
      Expr ex;
      if (!stmt.gotIdentifier(id)) goto giveUp;
      if (!stmt.strip().length) continue; // ignore this kind of #define.
      // logln("parse expr ", stmt, "; id '", id, "'");
      auto backup = stmt;
      if (!gotIntExpr(stmt, ex) || stmt.strip().length) {
        stmt = backup;
        bool isMacroParams(string s) {
          if (!s.accept("(")) return false;
          while (true) {
            string id;
            if (!s.gotIdentifier(id) || !s.accept(",")) break;
          }
          if (!s.accept(")")) return false;
          return true;
        }
        if (isMacroParams(stmt)) goto giveUp;
        // logln("full-parse ", stmt, " | ", start);
        // muahaha
        try {
          try {
            if (!rest(stmt, "tree.expr.literal", &ex) || stmt.strip().length) {
              goto alternative;
            }
          } catch (Exception ex)
            goto alternative;
          if (false) alternative:
            if (!rest(stmt, "tree.expr", &ex))
              goto giveUp;
        } catch (Exception ex)
          goto giveUp; // On Error Fuck You
      }
      auto ea = new ExprAlias(ex, id);
      // logln("got ", ea);
      add(id, ea);
      continue;
    }
    bool isTypedef;
    if (stmt.accept("typedef")) isTypedef = true;
    if (stmt.accept("enum")) {
      auto entries = stmt.between("{", "}").split(",");
      Expr cur = new IntExpr(0);
      Named[] elems;
      foreach (entry; entries) {
        // logln("> ", entry);
        string id;
        if (!gotIdentifier(entry, id)) {
          stmt = entry;
          goto giveUp;
        }
        if (entry.accept("=")) {
          Expr ex;
          if (!rest(entry, "tree.expr", &ex) || entry.strip().length) {
            // logln("--", entry);
            goto giveUp;
          }
          cur = foldex(ex);
        }
        elems ~= new ExprAlias(cur, id);
        cur = foldex(lookupOp("+", cur, new IntExpr(1)));
      }
      // logln("Got from enum: ", elems);
      stmt = stmt.between("}", "");
      string name;
      if (stmt.strip().length && (!gotIdentifier(stmt, name) || stmt.strip().length)) {
        // logln("fail on '", stmt, "'");
        goto giveUp;
      }
      foreach (elem; elems) add(elem.getIdentifier(), elem);
      if (name)
        add(name, new TypeAlias(Single!(SysInt), name));
      continue;
    }
    bool isUnion;
    auto st2 = stmt;
    if (st2.accept("struct") || (st2.accept("union") && (isUnion = true, true))) {
      string ident;
      gotIdentifier(st2, ident);
      if (st2.accept("{")) {
        auto startstr = st2;
        auto st = new Structure(ident);
        st.isUnion = isUnion;
        while (true) {
          if (st2.startsWith("#define"))
            goto skip;
          auto ty = matchType(st2);
          // logln("match type @", st2, " = ", ty);
          if (!ty) goto giveUp1;
          while (true) {
            auto pos = st2.find("sizeof");
            if (pos == -1) break;
            auto block = st2[pos .. $].between("(", ")");
            auto sty = matchType(block);
            if (!sty) {
              goto giveUp1;
            }
            auto translated = Format(sty.size);
            st2 = st2[0 .. pos] ~ translated ~ st2[pos .. $].between(")", "");
            // logln("st2 => ", st2);
          }
          string name3;
          auto st3 = st2;
          Expr size;
          st3 = st3.replace("(int)", ""); // hax
          if (gotIdentifier(st3, name3) && st3.accept("[") && rest(st3, "tree.expr", &size) && st3.accept("]")) {
            redo:
            size = foldex(size);
            if (cast(AstTuple) size.valueType()) {
              // unwrap "(foo)"
              size = (cast(StructLiteral) (cast(RCE) size).from)
                .exprs[$-1];
              goto redo;
            }
            auto ie = cast(IntExpr) size;
            // logln("size: ", size);
            if (!ie) goto giveUp1;
            new RelMember(name3, new StaticArray(ty, ie.num), st);
            // logln("rest: ", st3);
            if (st3.strip().length) {
              goto giveUp1;
            }
            goto skip;
          }
          // logln(">> ", st2);
          if (st2.find("(") != -1) {
            // alias to void for now.
            add(ident, new TypeAlias(Single!(Void), ident));
            goto giveUp1; // can't handle yet
          }
          foreach (var; st2.split(",")) {
            new RelMember(var.strip(), ty, st);
          }
        skip:
          st2 = statements.take();
          if (st2.accept("}")) break;
        }
        auto name = st2.strip();
        if (!name.length) name = ident;
        add(name, st);
        continue;
        giveUp1:
        while (true) {
          // logln("stmt: ", st2, " in ", startstr);
          st2 = statements.take();
          if (st2.accept("}")) break;
        }
        // logln(">>> ", st2);
        continue;
      }
    }
    if (isTypedef) {
      auto target = matchType(stmt);
      string name;
      if (!target) goto giveUp;
      if (stmt.accept("{")) {
        while (true) {
          stmt = statements.take();
          if (stmt.accept("}")) break;
        }
      }
      if (!gotIdentifier(stmt, name)) goto giveUp;
      string typename = name;
      if (matchSimpleType(typename) && !typename.strip().length) {
        // logln("Skip type ", name, " for duplicate. ");
        continue;
      }
      Expr size;
      redo2:
      auto st3 = stmt;
      if (st3.accept("[") && rest(st3, "tree.expr", &size) && st3.accept("]")) {
        redo3:
        size = foldex(size);
        // unwrap "(bar)" again
        if (cast(AstTuple) size.valueType()) {
          size = (cast(StructLiteral) (cast(RCE) size).from).exprs[$-1];
          goto redo3;
        }
        if (!cast(IntExpr) size) goto giveUp;
        target = new StaticArray(target, (cast(IntExpr) size).num);
        stmt = st3;
        goto redo2;
      }
      if (stmt.accept("[")) goto giveUp;
      auto ta = new TypeAlias(target, name);
      res ~= ta; cache[name] = ta;
      continue;
    }
    
    stmt.accept("extern");
    stmt = stmt.strip();
    if (auto rest = stmt.startsWith("__attribute__")) stmt = rest.between(") ", "");
    
    if (auto ret = stmt.matchType()) {
      string name;
      if (!gotIdentifier(stmt, name) || !stmt.accept("("))
        goto giveUp;
      IType[] args;
      while (true) {
        if (auto ty = matchParam(stmt)) args ~= ty;
        else break;
      }
      if (!stmt.accept(")")) goto giveUp;
      if (args.length == 1 && args[0] == Single!(Void))
        args = null; // C is stupid.
      auto fun = new Function;
      fun.name = name;
      fun.extern_c = true;
      fun.type = new FunctionType;
      fun.type.ret = ret;
      fun.type.params = args /map/ ex!(`a -> stuple(a, "")`);
      add(name, fun);
      continue;
    }
    giveUp:;
    // logln("Gave up on |", stmt, "| ", start);
  }
  auto ns = myNS.sup;
  // logln("Got ", res /map/ ex!("a -> a.getIdentifier()"));
  foreach (thing; res) {
    if (ns.lookup(thing.getIdentifier())) {
      // logln("Skip ", thing, " as duplicate. ");
      continue;
    }
    // logln("Add ", thing);
    ns.add(thing);
  }
  logln("Got ", res.length, " definitions from ", filename, " in ", sec() - start_time, "s. ");
}

import ast.fold, ast.literal_string;
Object gotCImport(ref string text, ParseCb cont, ParseCb rest) {
  if (!text.accept("c_include")) return null;
  Expr ex;
  if (!rest(text, "tree.expr", &ex))
    text.failparse("Couldn't find c_import string expr");
  if (!text.accept(";")) text.failparse("Missing trailing semicolon");
  auto str = cast(StringExpr) foldex(ex);
  if (!str)
    text.failparse(foldex(ex), " is not a string");
  auto name = str.str;
  // prevent injection attacks
  foreach (ch; name)
    if (!(ch in Range['a'..'z'].endIncl)
      &&!(ch in Range['A'..'Z'].endIncl)
      &&!(ch in Range['0' .. '9'].endIncl)
      &&("/_-.".find(ch) == -1)
    )
      throw new Exception("Invalid character in "~name~": "~ch~"!");
  // prevent snooping
  if (name.find("..") != -1)
    throw new Exception("Can't use .. in "~name~"!");
  
  string filename;
  if (name.exists()) filename = name;
  else {
    foreach (path; include_path) {
      auto combined = path.sub(name);
      if (combined.exists()) { filename = combined; break; }
    }
  }
  if (!filename) throw new Exception("Couldn't find "~name~"!");
  auto cmdline = 
    "gcc -m32 -Xpreprocessor -dD -E "
    ~ (include_path
      /map/ (string s) { return "-I"~s; }
      ).join(" ")
    ~ " " ~ filename;
  // logln("? ", cmdline);
  auto src = readback(cmdline);
  parseHeader(filename, src, rest);
  return Single!(NoOp);
}
mixin DefaultParser!(gotCImport, "tree.toplevel.c_import");
