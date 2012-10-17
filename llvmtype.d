module llvmtype;

import casts, llvmfile, quickformat;
import ast.base, ast.int_literal, ast.types, ast.pointer, ast.static_arrays, ast.arrays, ast.fun;
import tools.log, tools.base: strip, startsWith, endsWith;

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
  s = s.strip();
  string res;
  bool eat(string mark) { s = s.strip(); if (auto rest = s.startsWith(mark)) { s = rest; res ~= " "; res ~= mark; res ~= " "; return true; } return false; }
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
  return res;
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

extern(C) string[] structDecompose(string str) {
  auto main = str.startsWith("{").endsWith("}");
  if (!main) fail;
  string[] res;
  while (main.length) {
    res ~= eatType(main);
    main = main.strip();
    if (auto rest = main.startsWith(",")) { main = rest; continue; }
    break;
  }
  if (main.length) {
    logln("unexpected text in struct ", str, ": ", main);
    fail;
  }
  return res[];
}
