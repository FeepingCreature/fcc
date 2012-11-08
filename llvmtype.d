module llvmtype;

import casts, llvmfile, quickformat;
import ast.base, ast.int_literal, ast.types, ast.pointer, ast.static_arrays, ast.arrays, ast.fun;
import tools.log, tools.base: strip, between;
import parseBase: startsWith, endsWith;

extern(C) string typeToLLVM(IType it, bool subst = false) {
  // logln("typeToLLVM ", it);
  if (!it) fail;
  if (Single!(Pointer, Single!(Void)) == it) return "i8*";
  if (subst) { // asked to substitute a simpler type
    it = resolveType(it);
    if (Single!(Void) == it) return "{}"; // weirdo.
    if (auto arr = fastcast!(Array)(it)) {
      return typeToLLVM(Single!(Array, Single!(Byte)));
    }
    if (auto poi = fastcast!(Pointer)(it)) {
      return typeToLLVM(Single!(Pointer, Single!(Byte)));
    }
    if (auto fp = fastcast!(FunctionPointer)(it)) {
      return typeToLLVM(fastalloc!(FunctionPointer)(Single!(Void), cast(Argument[]) null));
    }
  }
  if (it.llvmType().find("void*") != -1) {
    logln(it);
    logln(it.llvmType());
    fail;
  }
  return it.llvmType();
}

extern(C) int guessSize(IType it) {
  if (auto ie = fastcast!(IntExpr)(llvmval(it.llvmSize()))) {
    return ie.num;
  }
  todo(qformat("guessSize(", it, " ", it.llvmSize(), ")"));
  return 0;
}

extern(C) Expr llvmvalstr(string s) {
  auto val = my_atoi(s);
  if (qformat(val) == s) return mkInt(val);
  return fastalloc!(LLVMValue)(s);
}

string eatType(ref string s) {
  auto first_s = s;
  s = s.mystripl();
  bool eat(string mark) {
    s = s.mystripl();
    if (auto rest = s.startsWith(mark)) {
      s = rest;
      return true;
    }
    return false; 
  }
  string base;
  void matchType() {
    if (eat("{")) {
      while (!eat("}")) do matchType(); while (eat(","));
      goto try_appends;
    }
    if (eat("<")) {
      auto t = s;
      auto num = t.slice("x").my_atoi();
      if (!eat(qformat(num)) || !eat("x")) {
        logln("weird vector ", first_s, " at ", s);
        fail;
      }
      matchType();
      if (!eat(">")) {
        logln("weird vector ", first_s, " at ", s);
        fail;
      }
      goto try_appends;
    }
    if (eat("[")) {
      auto t = s;
      auto num = t.slice("x").my_atoi();
      if (!eat(qformat(num)) || !eat("x")) {
        logln("weird SA ", first_s, " at ", s);
        fail;
      }
      matchType();
      if (!eat("]")) {
        logln("weird SA ", first_s, " at ", s);
        fail;
      }
      goto try_appends;
    }
    if (!eat("i64") && !eat("i32") && !eat("i16") && !eat("i8")
      &&!eat("float") && !eat("double") && !eat("void"))
    {
      logln("unable to match basic type: ", first_s, " at ", s);
      fail;
    }
  try_appends:
    if (eat("*")) goto try_appends;
    if (eat("(")) {
      while (!eat(")")) do matchType; while (eat(","));
      goto try_appends;
    }
  }
  matchType;
  return first_s.ptr[0..s.ptr-first_s.ptr].mystrip();
}

string[] getVecTypes(string str) {
  if (auto rest = str.startsWith("<")) str = rest;
  else fail;
  int len = str.slice("x").my_atoi();
  auto type = str.endsWith(">").strip();
  if (!type) fail;
  string[] res = new string[len];
  foreach (ref r; res) r = type;
  return res;
}

alias void delegate(string) structDecompose_dg;
extern(C) void structDecompose(string str, structDecompose_dg dg) {
  auto main = str.startsWith("{").endsWith("}").strip();
  if (!main) return;
  while (main.length) {
    dg(eatType(main));
    main = main.strip();
    if (auto rest = main.startsWith(",")) { main = rest; continue; }
    break;
  }
  if (main.length) {
    logln("unexpected text in struct ", str, ": ", main);
    fail;
  }
}

// produce a type that has the same layout as s, but with simplified types.
// for instance, changing any pointer to i8*.
string canonifyType(string s, bool dryrun = false) {
  s = s.strip();
  if (s.endsWith("*")) return "i32";
  if (s.endsWith("}")) {
    bool changed;
    structDecompose(s, (string type) {
      if (changed) return; // no need to test further
      if (canonifyType(type, true)) changed = true;
    });
    if (dryrun) return changed?"y":null;
    else if (!changed) return s;
    
    string res;
    structDecompose(s, (string type) {
      if (res) res ~= ", ";
      res ~= canonifyType(type);
    });
    return qformat("{", res, "}");
  }
  if (dryrun) return null;
  return s;
}

string eat_canonify(ref string s) {
  void eat(ref string s, string mark) {
    if (auto rest = s.startsWith(mark)) s = rest;
    else { logln("?", mark, " #### ", s); fail; }
  }
  if (auto rest = s.startsWith("ptrtoint(")) {
    auto desttype = eatType(rest);
    eat(rest, "getelementptr(");
    auto srctype = eatType(rest);
    eat(rest, "null");
    if (auto r2 = desttype.endsWith("*")) desttype = r2;
    else fail;
    if (auto r2 = srctype.endsWith("*")) srctype = r2;
    else fail;
    if (auto r2 = rest.startsWith(", i32 1) to i32)")) {
      s = r2;
      if (srctype != desttype) fail;
      desttype = canonifyType(desttype);
      srctype = canonifyType(srctype);
      return qformat("ptrtoint(", desttype, "* getelementptr(", srctype, "* null, i32 1) to i32)");
    }
    auto mew = rest.between("", ") to i32)");
    if (mew && mew.find("(") == -1 && mew.find(")") == -1) { // easy fallback
      s = rest.between(") to i32)", "");
      return qformat("ptrtoint(", desttype, "* getelementptr(", srctype, "* null", mew, ") to i32)");
    }
    logln("? ", rest);
    fail;
  }
  if (auto rest = s.startsWith("select(i1 icmp sgt(i32 ")) {
    auto va = eat_canonify(rest);
    eat(rest, ", i32 ");
    auto vb = eat_canonify(rest);
    eat(rest, "), i32 ");
    auto va2 = eat_canonify(rest);
    if (va != va2) {
      logln("VA  ", va);
      logln("VA2 ", va2);
      fail;
    }
    eat(rest, ", i32 ");
    auto vb2 = eat_canonify(rest);
    if (vb != vb2) {
      logln("VB  ", vb);
      logln("VB2 ", vb2);
      fail;
    }
    eat(rest, ")");
    s = rest;
    return qformat("select(i1 icmp sgt(i32 ", va, ", i32 ", vb, "), i32 ", va, ", i32 ", vb, ")");
  }
  {
    auto s1 = s.between("", ","), s2 = s.between("", ")");
    string str = s;
    if (s1 && s1.length < str.length) str = s1;
    if (s2 && s2.length < str.length) str = s2;
    auto testnum = str.my_atoi(), test = qformat(testnum);
    if (auto rest = s.startsWith(test)) {
      s = rest;
      return test;
    }
  }
  logln("? canonify ", s);
  fail;
}

extern(C) string canonify(string s) {
  auto res = eat_canonify(s);
  if (s.length) {
    logln("? ", s);
    fail;
  }
  return res;
}
