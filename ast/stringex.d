module ast.stringex;

import
  ast.base, ast.parse, ast.concat, ast.namespace, ast.scopes, ast.static_arrays,
  ast.literals, ast.arrays, ast.vardecl, ast.pointer, ast.casting, tools.base: take;

Object gotStringEx(ref string text, ParseCb cont, ParseCb rest) {
  Expr strlit;
  auto t2 = text;
  // if (!t2.accept("^")) return null;
  if (!gotStringExpr(t2, strlit)) return null;
  text = t2;
  auto str = (cast(StringExpr) strlit).str;
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
        bool tryFormat(Expr ex) {
          if (auto sf = simpleFormat(ex)) {
            res.addArray(sf);
            return true;
          } else if (auto fe = cast(Formatable) ex.valueType()) {
            res.addArray(fe.format(ex));
            return true;
          } else return false;
        }
        bool foundMatch;
        auto ex2 = ex;
        gotImplicitCast(ex2,  &tryFormat);
        if (!ex2)
          throw new Exception(Format("Can't format ", ex, " of ", ex.valueType()));
      }
    }
  }
  if (!extended) return cast(Object) strlit;
  flush;
  return res;
}
mixin DefaultParser!(gotStringEx, "tree.expr.literal.stringex", "550");

import ast.dg, ast.tuples, ast.tuple_access;
Expr simpleFormat(Expr ex) {
  auto type = ex.valueType();
  if (Single!(SysInt) == type) {
    return iparse!(Expr, "gen_int_format", "tree.expr")
    ("itoa(ex)", "ex", ex);
  }
  if (Single!(Float) == type) {
    return iparse!(Expr, "gen_float_format", "tree.expr")
    ("ftoa(ex)", "ex", ex);
  }
  if (auto p = cast(Pointer) type) {
    return iparse!(Expr, "gen_ptr_format", "tree.expr")
    ("ptoa(cast(void*) ex)", "ex", ex);
  }
  if (auto sa = cast(StaticArray) type) {
    ex = staticToArray(ex);
    type = ex.valueType();
  }
  if (auto dg = cast(Delegate) type) {
    return iparse!(Expr, "gen_dg_format", "tree.expr")
      (`"dg(fun $(cast(void*) dg.fun), data $(cast(void*) dg.data))"`,
        "dg", ex
      );
  }
  if (auto tup = cast(Tuple) type) {
    auto res = new ConcatChain(new StringExpr("{"));
    foreach (i, entry; getTupleEntries(ex)) {
      if (i) res.addArray(new StringExpr(", "));
      res.addArray(iparse!(Expr, "gen_tuple_member_format", "tree.expr.literal.stringex")(`"$entry"`, "entry", entry));
    }
    res.addArray(new StringExpr("}"));
    return res;
  }
  if (auto ar = cast(Array) type) {
    if (Single!(Char) == ar.elemType) {
      return ex;
    }
    return new CallbackExpr(Single!(Array, Single!(Char)), ex /apply/ (Expr ex, AsmFile af) {
      mkVar(af, Single!(Array, Single!(Char)), true, (Variable var) {
        iparse!(Scope, "gen_array_format", "tree.scope")
        (`{
            char[~] res;
            res = res ~ "[";
            auto ar = array;
            for (int i = 0; i < ar.length; ++i) {
              if i res = res ~ ", ";
              auto elem = ar[i];
              res = res ~ "$elem";
            }
            res = res ~ "]";
            var = res[0 .. res.length];
          }`,
          namespace(),
          "var", var, "array", ex,
          af
        ).emitAsm(af);
      });
    });
  }
  return null;
}
