module ast.c_bind;

// Optimized for GL.h; may not work for others!! 
import ast.base, ast.modules;

import tools.compat, tools.functional;
alias asmfile.startsWith startsWith;

extern(C) {
  int pipe(int*);
  int close(int);
}

string readStream(InputStream IS) {
  string res;
  ubyte[512] buffer;
  int i;
  do {
    i = IS.read(buffer);
    if (i < 0) throw new Exception(Format("Read error: ", i));
    res ~= cast(string) buffer[0 .. i];
  } while (i);
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

import ast.aliasing, ast.pointer, ast.fun, ast.namespace;
void parseHeader(string filename, string src, ParseCb rest) {
  string newsrc;
  foreach (line; src.split("\n")) {
    if (line.startsWith("#define")) { newsrc ~= line; newsrc ~= ";"; }
    if (line.startsWith("#")) continue;
    newsrc ~= line;
  }
  // no need to remove comments; the preprocessor already did that
  auto statements = newsrc.split(";") /map/ &strip;
  // mini parser
  Named[] res;
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
    if (accept("unsigned int") || accept("signed int") || accept("int")) return Single!(SysInt);
    if (accept("unsigned char") || accept("signed char") || accept("char")) return Single!(Char);
    if (accept("unsigned short") || accept("short")) return Single!(Short);
    if (accept("void")) return Single!(Void);
    if (accept("float")) return Single!(Float);
    if (accept("double")) return Single!(Double);
    foreach (entry; res)
      if (accept(entry.getIdentifier())) return cast(IType) entry;
    if (accept("struct")) {
      string type;
      text.gotIdentifier(type); // ~Meh.
      return Single!(Void);
    }
    return null;
  }
  IType matchType(ref string text) {
    text.accept("const");
    if (auto ty = matchSimpleType(text)) {
      while (text.accept("*")) ty = new Pointer(ty);
      return ty;
    } else return null;
  }
  IType matchParam(ref string text) {
    IType ty = matchType(text);
    if (!ty) return null;
    string id;
    gotIdentifier(text, id);
    text.accept(",");
    return ty;
  }
  while (statements.length) {
    auto stmt = statements.take(), start = stmt;
    stmt.accept("__extension__");
    if (stmt.accept("#define")) {
      if (stmt.accept("__")) continue; // internal
      string id;
      Expr ex;
      if (!stmt.gotIdentifier(id)) goto giveUp;
      if (!stmt.strip().length) continue; // ignore this kind of #define.
      // logln("parse expr ", stmt);
      auto backup = stmt;
      try {
        if (!rest(stmt, "tree.expr.literal", &ex) || stmt.strip().length) {
          stmt = backup;
          if (!rest(stmt, "tree.expr", &ex))
            goto giveUp;
        }
      } catch (Exception ex)
        goto giveUp; // On Error Fuck You
      res ~= new ExprAlias(ex, id);
      continue;
    }
    if (stmt.accept("typedef")) {
      if (stmt.accept("enum")) {
        auto entries = stmt.between("{", "}").split(",");
        int count;
        Named[] elems;
        foreach (entry; entries) {
          string id;
          if (!gotIdentifier(entry, id) || entry.strip().length) {
            stmt = entry;
            goto giveUp;
          }
          elems ~= new ExprAlias(new IntExpr(count++), id);
        }
        // logln("Got from enum: ", elems);
        stmt = stmt.between("}", "");
        string name;
        if (!gotIdentifier(stmt, name) || stmt.strip().length)
          goto giveUp;
        res ~= elems;
        res ~= new TypeAlias(Single!(SysInt), name);
        continue;
      }
      auto target = matchType(stmt);
      string name;
      if (!target) goto giveUp;
      // TODO: handle structs properly
      if (stmt.accept("{")) {
        while (true) {
          stmt = statements.take();
          if (stmt.accept("}")) break;
        }
        // logln(">>> ", stmt);
      }
      if (!gotIdentifier(stmt, name)) goto giveUp;
      string typename = name;
      if (matchSimpleType(typename) && !typename.strip().length) {
        // logln("Skip type ", name, " for duplicate. ");
        continue;
      }
      res ~= new TypeAlias(target, name);
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
      res ~= fun;
      continue;
    }
    giveUp:;
    // logln("Giving up on |", stmt, "| ", start);
  }
  auto ns = namespace();
  // logln("Got ", res /map/ ex!("a -> a.getIdentifier()"));
  foreach (thing; res) {
    if (ns.lookup(thing.getIdentifier())) {
      // logln("Skip ", thing, " as duplicate. ");
      continue;
    }
    // logln("Add ", thing);
    ns.add(thing);
  }
  logln("Got ", res.length, " definitions from ", filename, ". ");
}

import ast.fold, ast.literals;
Object gotCImport(ref string text, ParseCb cont, ParseCb rest) {
  if (!text.accept("c_include")) return null;
  Expr ex;
  if (!rest(text, "tree.expr", &ex)) throw new Exception("Couldn't find expr at '"~text.next_text()~"'!");
  if (!text.accept(";")) throw new Exception("Missing trailing semicolon at '"~text.next_text()~"'! ");
  auto str = cast(StringExpr) fold(ex);
  if (!str) throw new Exception(Format(fold(ex), " is not a string at '", text.next_text(), "'!"));
  auto name = str.str;
  // prevent injection attacks
  foreach (ch; name)
    if (!(ch in Range['a'..'z'].endIncl)
      &&!(ch in Range['A'..'Z'].endIncl)
      &&!(ch in Range['0' .. '9'].endIncl)
      &&("/_.".find(ch) == -1)
    )
      throw new Exception("Invalid character in "~name~": "~ch~"!");
  // prevent snooping
  if (name.find("..") != -1)
    throw new Exception("Can't use .. in "~name~"!");
  
  string filename;
  if (name.exists()) filename = name;
  else if (("/usr/include/"~name).exists()) filename = "/usr/include/"~name;
  else throw new Exception("Couldn't find "~name~"!");
  auto src = readback("gcc -m32 -Xpreprocessor -dD -E "~filename);
  parseHeader(filename, src, rest);
  return Single!(NoOp);
}
mixin DefaultParser!(gotCImport, "tree.toplevel.c_import");
