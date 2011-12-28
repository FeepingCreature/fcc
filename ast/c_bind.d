module ast.c_bind;

// Optimized for GL.h and SDL.h; may not work for others!! 
import ast.base, ast.modules, ast.structure, ast.casting, ast.static_arrays, ast.externs, ast.tuples: AstTuple = Tuple;

import tools.compat, tools.functional;
alias asmfile.startsWith startsWith;

extern(C) {
  int pipe(int*);
  int close(int);
}

string buf;
string readStream(InputStream IS) {
  if (!buf) buf = new char[16384];
  int reslen;
  ubyte[16384] buffer;
  int i;
  do {
    i = IS.read(buffer);
    if (i < 0) throw new Exception(Format("Read error: ", i));
    while (buf.length < reslen + i)
      buf.length = cast(int) (buf.length * 2);
    buf[reslen .. reslen + i] = cast(string) buffer[0 .. i];
    reslen += i;
  } while (i);
  auto res = buf[0 .. reslen];
  buf = buf[reslen .. $];
  return res;
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

class LateType : IType {
  string name;
  IType me;
  void delegate() tryResolve;
  this(string n) { name = n; }
  string toString() { if (!me) return Format("(LateType (", name, "), unresolved)"); return Format("(LateType ", me, ")"); }
  void needMe() {
    if (!me) tryResolve();
    assert(!!me);
  }
  override {
    int size() { needMe; return me.size; }
    ubyte[] initval() { needMe; return me.initval; }
    bool isPointerLess() { needMe; return me.isPointerLess(); }
    bool isComplete() { return !!me; } // TODO: ??
    int opEquals(IType it) {
      auto lt = fastcast!(LateType) (it);
      if (lt && name == lt.name) return true;
      needMe;
      it = resolveType(it);
      return it is me || it == me;
    }
    string mangle() { needMe; return me.mangle(); }
    IType proxyType() { needMe; return me; }
  }
}

const c_tree_expr = "tree.expr"
  " >tree.expr.vardecl >tree.expr.type_stringof >tree.expr.type_mangleof"
  " >tree.expr.classid >tree.expr.iter >tree.expr.iter_range"
  " >tree.expr.new >tree.expr.eval >tree.expr.cast >tree.expr.veccon"
  " >tree.expr.cast_explicit_default >tree.expr.cast_convert"
  " >tree.expr.scoped >tree.expr.stringex >tree.expr.dynamic_class_cast"
  " >tree.expr.properties >tree.expr.veccon";

const c_tree_expr_matcher = matchrule_static(c_tree_expr);

TLS!(Expr delegate(ref string)) specialCallback;
static this() { New(specialCallback); }

bool parsingCHeader() {
  auto ns = namespace();
  while (ns) {
    auto mns = ns.get!(MiniNamespace);
    if (!mns) return false;
    if (mns.id == "parse_header") return true;
    ns = mns.sup;
  }
  return false;
}

void parseHeader(string filename, string src) {
  auto start_time = sec();
  string newsrc;
  bool inEnum;
  string[] buffer;
  void flushBuffer() { foreach (def; buffer) newsrc ~= def ~ ";"; buffer = null; }
  while (src.length) {
    string line = src.slice("\n");
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
  Named[string] cache;
  auto myNS = new MiniNamespace("parse_header");
  myNS.sup = namespace();
  myNS.internalMode = true;
  namespace.set(myNS);
  scope(exit) namespace.set(myNS.sup);
  void add(string name, Named n) {
    if (myNS.lookup(name)) { return; } // duplicate definition. meh.
    auto ea = fastcast!(ExprAlias)~ n;
    if (ea) {
      if (!gotImplicitCast(ea.base, (IType it) { return !fastcast!(AstTuple) (it); })) {
        logln("Weird thing ", ea);
        fail;
      }
    }
    // logln("add ", name, " <- ", n);
    myNS._add(name, fastcast!(Object)~ n);
    if (auto ns = fastcast!(Namespace) (n)) ns.sup = null; // lol
    cache[name] = n;
  }
  
  void delegate()[] resolves;
  scope(success)
    foreach (dg; resolves)
      dg();
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
    bool unsigned;
    if (accept("_Bool")) return Single!(Char);
    if (accept("unsigned")) unsigned = true;
    else accept("signed");
    
    if (accept("long")) {
      if (accept("int")) return Single!(SysInt);
      if (accept("long")) { accept("int"); return Single!(Long); }
      return unsigned?Single!(SizeT):Single!(SysInt);
    }
    if (accept("int")) return Single!(SysInt);
    if (accept("short")) { accept("int"); return Single!(Short); }
    if (accept("char")) return Single!(Char);
    if (unsigned) return Single!(SysInt);
    
    if (accept("void")) return Single!(Void);
    if (accept("float")) return Single!(Float);
    if (accept("double")) return Single!(Double);
    if (accept("struct")) {
      string name;
      if (!text.gotIdentifier(name))
        return Single!(Void);
      if (auto p = name in cache) return fastcast!(IType)~ *p;
      else {
        auto lt = new LateType(name);
        auto dg = stuple(lt, name, &cache) /apply/
        delegate void(LateType lt, string name, typeof(cache)* cachep) {
          if (auto p = name in *cachep) {
            lt.me = fastcast!(IType)~ *p;
            if (auto al = fastcast!(TypeAlias) (lt.me))
              if (al.base is lt) {
                logln("CIRCULAR TYPE: ", name);
                fail;
              }
          }
          // else assert(false, "'"~name~"' didn't resolve! ");
          else lt.me = Single!(Void);
        };
        lt.tryResolve = dg;
        resolves ~= dg;
        return lt;
      }
    }
    string id;
    if (!text.gotIdentifier(id)) return null;
    if (auto p = id in cache) return fastcast!(IType)~ *p;
    if (auto ty = fastcast!(IType) (namespace().lookup(id))) return ty;
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
    auto t2 = text;
    IType ty = matchType(t2);
    if (!ty) return null;
    text = t2;
    text.accept("__restrict");
    text.accept("__const");
    string id;
    gotIdentifier(text, id);
    if (auto sa = fastcast!(StaticArray)~ resolveType(ty)) {
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
  Stuple!(string[], string)[string] macros;
  bool[char*] loopbreaker; // recursion loop avoidance, lol
  bool readCExpr(ref string source, ref Expr res) {
    source = mystripl(source);
    if (!source.length) return false;
    auto s2 = source;
    // fairly obvious what this is
    if (source.endsWith("_TYPE") || s2.matchType()) return false;
    int i;
    s2 = source;
    {
      IType ty;
      if (s2.accept("(") && (ty = matchType(s2), ty) && s2.accept(")") && readCExpr(s2, res)) {
        IType alt;
        if (ty == Single!(Char)) alt = Single!(Byte); // same type in C
        res = foldex(forcedConvert(res));
        // res = reinterpret_cast(ty, res);
        if (!gotImplicitCast(res, ty, (IType it) { return test(it == ty || alt && it == alt); }))
          return false;
        source = s2;
        return true;
      }
    }
    if (s2.accept("'")) { // char
      if (!s2.length) return false;
      auto ch = s2[0..1]; s2 = s2[1 .. $];
      if (!s2.accept("'")) return false;
      res = reinterpret_cast(Single!(Char), new DataExpr(cast(ubyte[]) ch));
      source = s2;
      return true;
    }
    if (s2.gotInt(i)) {
      if (auto rest = s2.startsWith("U")) s2 = rest; // TODO
      if (s2.accept("LL")) return false; // long long
      s2.accept("L");
      if (!s2.length /* special handling for separators */ || s2.startsWith(",") || s2.startsWith(")")) {
        res = new IntExpr(i);
        source = s2;
        return true;
      }
    }
    s2 = source;
    if (s2.startsWith("__PRI")) return false; // no chance to parse
    s2 = source;
    string ident;
    if (s2.gotIdentifier(ident) && !s2.length) {
      // float science notation constants
      if (ident.length > 2) {
        if (ident[0] == 'e' || ident[0] == 'E')
          if (ident[1] == '+' || ident[1] == '-') return false;
        if (ident[0] == '1' && (ident[1] == 'e' || ident[1] == 'E'))
          if (ident[2] == '+' || ident[2] == '-') return false;
      }
      if (auto p = ident in cache) {
        if (auto ex = fastcast!(Expr)~ *p) {
          res = ex;
          source = null;
          return true;
        }
        return false;
      }
      // logln("IDENT ", ident);
    }
    if (auto tup = ident in macros) {
      auto backup = s2;
      auto args = tup._0, str = tup._1;
      // logln("macro parse for ", ident, " on ", s2);
      if (!s2.accept("(")) return false;
      Object[] objs;
      while (true) {
        Expr ex;
        if (readCExpr(s2, ex)) objs ~= fastcast!(Object) (ex);
        else if (auto ty = matchType(s2)) objs ~= fastcast!(Object) (ty);
        else {
          // logln("macro arg fail ", s2);
          return false;
        }
        if (!s2.accept(",")) break;
      }
      if (!s2.accept(")")) {
        // logln("fail 2 on ", s2);
        return false;
      }
      if (objs.length != args.length) {
        // logln("length fail");
        return false;
      }
      auto myNS2 = new MiniNamespace("parse_macro");
      myNS2.sup = namespace();
      myNS2.internalMode = true;
      namespace.set(myNS2);
      scope(exit) namespace.set(myNS2.sup);
      foreach (k, arg; objs) {
        // logln(args[k], " -> ", arg);
        myNS2._add(args[k], arg);
      }
      pushCache;
      scope(exit) popCache;
      if (!readCExpr(str, res)) {
        // logln("macro fail ", str);
        return false;
      }
      opt(res);
      // logln(ident, " -- ", backup, " (args ", tup._0, ", str ", tup._1, ") => ", objs, " => ", res);
      source = s2;
      return true;
    }
    s2 = source;
    if (s2.startsWith("__attribute__ ((")) s2 = s2.between("))", "");
    // logln(" @ '", source, "'");
    s2 = s2.mystripl();
    if (!s2.length) return false;
    auto old_dg = *specialCallback();
    Expr callback(ref string text) {
      auto tp = text.ptr;
      if (tp in loopbreaker) return null;
      loopbreaker[tp] = true;
      scope(exit) loopbreaker.remove(tp);
      Expr res;
      if (readCExpr(text, res)) return res;
      if (old_dg) if (auto res = old_dg(text)) return res;
      return null;
    }
    *specialCallback() = &callback;
    scope(exit) *specialCallback() = old_dg;
    try res = fastcast!(Expr) (parsecon.parse(s2, mixin(c_tree_expr_matcher)));
    catch (Exception ex) return false; // no biggie
    if (!res) return false;
    source = s2;
    return true;
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
        string[] macroArgs;
        bool isMacroParams(ref string s) {
          auto s2 = s;
          if (!s2.accept("(")) return false;
          while (true) {
            string id;
            if (!s2.gotIdentifier(id)) break;
            macroArgs ~= id;
            if (!s2.accept(",")) break;
          }
          if (!s2.accept(")")) return false;
          s = s2;
          return true;
        }
        if (isMacroParams(stmt)) {
          macros[id] = stuple(macroArgs, stmt);
          // logln("macro: ", id, " (", macroArgs, ") => ", stmt);
          continue;
        }
        // logln("full-parse ", stmt, " | ", start);
        // muahaha
        try {
          try {
            if (!readCExpr(stmt, ex) || stmt.strip().length) {
              goto alternative;
            }
          } catch (Exception ex)
            goto alternative;
          if (false) {
            alternative:
            if (!readCExpr(stmt, ex))
              goto giveUp;
          }
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
      Expr cur = mkInt(0);
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
          if (!readCExpr(entry, ex) || entry.strip().length) {
            // logln("--", entry);
            goto giveUp;
          }
          cur = foldex(ex);
        }
        elems ~= new ExprAlias(cur, id);
        cur = foldex(lookupOp("+", cur, mkInt(1)));
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
    {
      auto st2 = stmt;
      if (st2.accept("struct") || (st2.accept("union") && (isUnion = true, true))) {
        string ident;
        gotIdentifier(st2, ident);
        if (st2.accept("{")) {
          auto startstr = st2;
          auto st = new Structure(ident);
          // st.minAlign = 4;
          st.isUnion = isUnion;
          while (true) {
            if (st2.startsWith("#define"))
              goto skip;
            auto ty = matchType(st2);
            // logln("for ", ident, ", match type @", st2, " = ", ty);
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
            if (gotIdentifier(st3, name3) && st3.accept("[") && readCExpr(st3, size) && st3.accept("]")) {
              redo:
              size = foldex(size);
              if (fastcast!(AstTuple)~ size.valueType()) {
                // unwrap "(foo)"
                logln("at ", st2.nextText(), ":");
                logln("unwrap ", (cast(Object) size).classinfo.name, " ", size);
                size = (fastcast!(StructLiteral)~ (fastcast!(RCE)~ size).from)
                  .exprs[$-1];
                goto redo;
              }
              auto ie = fastcast!(IntExpr)~ size;
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
              if (ty == Single!(Void)) goto giveUp1;
              new RelMember(var.strip(), ty, st);
            }
          skip:
            st2 = statements.take();
            if (st2.accept("}")) break;
          }
          auto name = st2.strip();
          if (!name.length) name = ident;
          if (!st.name.length) st.name = name;
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
      if (!gotIdentifier(stmt, name)) {
        auto st2 = stmt;
        if (!st2.accept("(") || !st2.accept("*") || !gotIdentifier(st2, name) || !st2.accept(")"))
          goto giveUp;
        // function pointer
        if (!st2.accept("(")) goto giveUp;
        Argument[] args;
        do {
          auto partype = matchType(st2);
          string parname;
          st2.gotIdentifier(parname);
          args ~= Argument(partype);
        } while (st2.accept(","));
        if (!st2.accept(")")) goto giveUp;
        // logln("get function pointer named ", name, " (ret ", target, ") , params ", args, " @", st2);
        target = new FunctionPointer(target, args);
        stmt = st2;
      }
      string typename = name;
      if (matchSimpleType(typename) && !typename.strip().length) {
        // logln("Skip type ", name, " for duplicate. ");
        continue;
      }
      Expr size;
      redo2:
      auto st3 = stmt;
      if (st3.accept("[") && readCExpr(st3, size) && st3.accept("]")) {
        redo3:
        size = foldex(size);
        // unwrap "(bar)" again
        if (fastcast!(AstTuple)~ size.valueType()) {
          size = (fastcast!(StructLiteral)~ (fastcast!(RCE)~ size).from).exprs[$-1];
          goto redo3;
        }
        if (!fastcast!(IntExpr) (size)) goto giveUp;
        target = new StaticArray(target, (fastcast!(IntExpr)~ size).num);
        stmt = st3;
        goto redo2;
      }
      if (stmt.accept("[")) goto giveUp;
      if (stmt.length) {
        auto st4 = stmt;
        if (st4.accept("__attribute__") && st4.accept("((")
        &&  st4.accept("__mode__") && st4.accept("(")) {
          if (resolveType(target) == Single!(SysInt)) {
            if (st4.accept("__QI__") && st4.accept(")") && st4.accept("))")) {
              stmt = st4;
              target = Single!(Byte);
            }
            else if (st4.accept("__HI__") && st4.accept(")") && st4.accept("))")) {
              stmt = st4;
              target = Single!(Short);
            }
            else if (st4.accept("__SI__") && st4.accept(")") && st4.accept("))")) {
              stmt = st4;
              // int already
            }
            else if (st4.accept("__DI__") && st4.accept(")") && st4.accept("))")) {
              stmt = st4;
              target = Single!(Long);
            }
          }
        }
        if (stmt.strip().length) {
          // logln("LEFTOVER: ", stmt);
          // logln("(target ", target, " = ", name, ")");
          goto giveUp;
        }
      }
      if (auto proxy = fastcast!(LateType) (target))
        if (proxy.name == name)
          target = Single!(Void); // would set up a loop .. produce _something_
      
      auto ta = new TypeAlias(target, name);
      cache[name] = ta;
      continue;
    }
    
    bool useStdcall;
    void eatAttribute(ref string s) {
      retry: s = s.strip();
      if (auto rest = s.startsWith("__attribute__")) {
        if (rest.between("((", "))") == "__stdcall__") useStdcall = true;
        s = rest.between(") ", "");
        goto retry;
      }
    }
    stmt.accept("extern");
    stmt.eatAttribute();
    
    if (auto ret = stmt.matchType()) {
      stmt.eatAttribute();
      string name;
      if (!gotIdentifier(stmt, name))
        goto giveUp;
      if (!stmt.accept("(")) {
        // weird, but, nope.
        // while (stmt.accept("[]")) ret = new Pointer(ret);
        if (stmt.accept("[]") && !stmt.length) {
          add(name, new ExprAlias(reinterpret_cast(new Pointer(ret), new RefExpr(new ExternCGlobVar(ret, name))), name));
          continue;
        }
        if (!stmt.length) {
          add(name, new ExternCGlobVar(ret, name));
          continue;
        }
        // logln("MEEP ", name, ", '", stmt, "'");
        goto giveUp;
      }
      IType[] args;
      // logln(name, "@ ", stmt, ", get types");
      while (true) {
        if (auto ty = matchParam(stmt)) args ~= ty;
        else break;
      }
      if (!stmt.accept(")")) goto giveUp;
      if (args.length == 1 && args[0] == Single!(Void))
        args = null; // C is stupid.
      foreach (ref arg; args)
        if (resolveType(arg) == Single!(Short))
          arg = Single!(SysInt);
      auto fun = new Function;
      fun.name = name;
      fun.extern_c = true;
      fun.type = new FunctionType;
      fun.type.ret = ret;
      fun.type.params = args /map/ (IType it) { return Argument(it); };
      fun.type.stdcall = useStdcall;
      fun.sup = null;
      add(name, fun);
      continue;
    }
    giveUp:;
    // logln("Gave up on |", stmt, "| ", start);
  }
  auto ns = myNS.sup;
  foreach (key, value; cache) {
    if (ns.lookup(key)) {
      // logln("Skip ", key, " as duplicate. ");
      continue;
    }
    // logln("Add ", value);
    ns.add(key, value);
  }
  // logSmart!(false)("# Got ", cache.length, " definitions from ", filename, " in ", sec() - start_time, "s. ");
}

void performCImport(string name) {
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
  if (!filename)
    throw new Exception(Format("Couldn't find ", name, "! Tried ", include_path));
  string extra;
  if (!isARM) extra = "-m32";
  auto cmdline = 
    platform_prefix~"gcc "~extra~" -Xpreprocessor -dD -E "
    ~ (include_path
      /map/ (string s) { return "-I"~s; }
      ).join(" ")
    ~ " " ~ filename;
  // logln("? ", cmdline);
  auto src = readback(cmdline);
  parseHeader(filename, src);
}

import ast.fold, ast.literal_string;
Object gotCImport(ref string text, ParseCb cont, ParseCb rest) {
  if (!text.accept("c_include")) return null;
  Expr ex;
  if (!rest(text, "tree.expr", &ex))
    text.failparse("Couldn't find c_import string expr");
  if (!text.accept(";")) text.failparse("Missing trailing semicolon");
  auto str = fastcast!(StringExpr)~ foldex(ex);
  if (!str)
    text.failparse(foldex(ex), " is not a string");
  performCImport(str.str);
  return Single!(NoOp);
}
mixin DefaultParser!(gotCImport, "tree.toplevel.c_import");

import ast.fold, ast.literal_string;
Object gotSpecialCallback(ref string text, ParseCb cont, ParseCb rest) {
  Expr ex;
  auto dg = *specialCallback();
  if (!dg) return null;
  auto t2 = text;
  auto res = dg(t2);
  if (!res) return null;
  text = t2;
  return fastcast!(Object) (res);
}
mixin DefaultParser!(gotSpecialCallback, "tree.expr.special_callback", "999"); // not super important

static this() {
  ast.modules.specialHandler = delegate Module(string name) {
    auto hdr = name.startsWith("c.");
    if (!hdr) return null;
    auto hfile = hdr.replace(".", "/") ~ ".h";
    
    auto mod = new Module(name, hfile);
    mod.dontEmit = true;
    
    auto backup = namespace();
    namespace.set(mod);
    scope(exit) namespace.set(backup);
    
    performCImport(hfile);
    return mod;
  };
}
