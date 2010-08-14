module ast.stringex;

import
  ast.base, ast.parse, ast.concat, ast.namespace, ast.scopes, ast.static_arrays,
  ast.literals, ast.arrays, ast.vardecl, ast.pointer, tools.base: take;

Object gotStringEx(ref string text, ParseCb cont, ParseCb rest) {
  Expr strlit;
  auto t2 = text;
  // if (!t2.accept("^")) return null;
  if (!gotStringExpr(t2, strlit)) return null;
  text = t2;
  auto str = (cast(StringExpr) strlit).str;
  logln("exstr ", str);
  auto res = new ConcatChain(new StringExpr(""));
  string buf;
  void flush() { if (!buf) return; res.addArray(new StringExpr(buf)); buf = null; }
  bool extended;
  while (str.length) {
    auto ch = str.take();
    if (ch == '\\') buf ~= str.take();
    else {
      if (ch != '$') buf ~= ch;
      else {
        extended = true;
        flush;
        assert(str.length);
        Expr ex;
        if (auto left = str.startsWith("$")) {
          if (!rest(left, "tree.expr", &ex))
            throw new Exception("Failed to parse expr from '"~left.next_text()~"'");
          str = left;
        } else if (auto left = str.startsWith("(")) {
          if (!rest(left, "tree.expr", &ex))
            throw new Exception("Failed to parse expr from '"~left.next_text()~"'");
          if (!left.accept(")"))
            throw new Exception("Unmatched expr in '"~left.next_text()~"'");
          str = left;
        } else {
          string id;
          if (!str.gotIdentifier(id))
            throw new Exception("Can't parse identifier from expansion string at '"~str~"'");
          ex = cast(Expr) namespace().lookup(id);
          if (!ex)
            throw new Exception("No such variable: "~id);
        }
        if (auto sf = simpleFormat(ex)) {
          res.addArray(sf);
        } else if (auto fe = cast(Formatable) ex.valueType()) {
          res.addArray(fe.format(ex));
        } else throw new Exception(Format("Can't format ", ex, " of ", ex.valueType()));
      }
    }
  }
  if (!extended) return cast(Object) strlit;
  flush;
  return res;
}
mixin DefaultParser!(gotStringEx, "tree.expr.literal.stringex", "550");

Expr simpleFormat(Expr ex) {
  auto type = ex.valueType();
  if (Single!(SysInt) == type) {
    return iparse!(Expr, "gen_int_format", "tree.expr")
    ("itoa(ex)", "ex", ex);
  }
  if (auto p = cast(Pointer) type) {
    return iparse!(Expr, "gen_ptr_format", "tree.expr")
    ("ptoa(cast(void*) ex)", "ex", ex);
  }
  if (auto sa = cast(StaticArray) type) {
    ex = staticToArray(ex);
    type = ex.valueType();
  }
  if (auto ar = cast(Array) type) {
    if (Single!(Char) == ar.elemType) {
      return ex;
    }
    auto res = new ConcatChain(new StringExpr("["));
    return new CallbackExpr(Single!(Array, Single!(Char)), ex /apply/ (Expr ex, AsmFile af) {
      mkVar(af, Single!(Array, Single!(Char)), true, (Variable var) {
        iparse!(Scope, "gen_array_format", "tree.scope")
        (`{
            var = "[";
            for (int i = 0; i < array.length; ++i) {
              if i var ~= ", ";
              auto elem = array[i];
              var ~= "$elem";
            }
            var ~= "]";
          }`,
          "var", var, "array", ex
        ).emitAsm(af);
      });
    });
  }
  return null;
}
