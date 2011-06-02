module ast.stringex;

import
  ast.base, ast.parse, ast.concat, ast.namespace, ast.scopes, ast.static_arrays, ast.assign,
  ast.literal_string, ast.arrays, ast.vardecl, ast.pointer, ast.casting, tools.base: take;

Object gotStringEx(ref string text, ParseCb cont, ParseCb rest) {
  Expr strlit;
  auto t2 = text;
  // if (!t2.accept("^")) return null;
  if (!gotStringExpr(t2, strlit)) return null;
  text = t2;
  auto str = (fastcast!(StringExpr)~ strlit).str;
  auto res = new ConcatChain(new StringExpr(""));
  string buf;
  void flush() { if (!buf) return; res.addArray(new StringExpr(buf)); buf = null; }
  bool extended;
  auto backup = str;
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
            left.failparse("Failed to parse expr");
          str = left;
        } else if (auto left = str.startsWith("(")) {
          if (!rest(left, "tree.expr", &ex))
            left.failparse("Failed to parse expr");
          if (!left.accept(")"))
            left.failparse("Unmatched expr");
          str = left;
        } else {
          string id;
          if (!str.gotIdentifier(id))
            throw new Exception("Can't parse identifier from expansion string at '"~str~"'");
          retry:
          ex = fastcast!(Expr)~ namespace().lookup(id);
          if (!ex)
            if (str.eatDash(id)) goto retry;
            else throw new Exception(Format("No such variable: ", id, " in ", namespace()));
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
        if (!gotImplicitCast(ex2,  &tryFormat))
          throw new Exception(Format("Can't format ", ex, " of ", ex.valueType()));
      }
    }
  }
  if (!extended) return fastcast!(Object)~ strlit;
  flush;
  return res;
}
mixin DefaultParser!(gotStringEx, "tree.expr.literal.stringex", "550");

import ast.dg, ast.tuples, ast.tuple_access, ast.funcall, ast.fun, ast.modules;
Expr simpleFormat(Expr ex) {
  auto type = resolveType(ex.valueType());
  if (Single!(SysInt) == type || Single!(Short) == type || Single!(Byte) == type) {
    return buildFunCall(fastcast!(Function)~ sysmod.lookup("itoa"), ex, "itoa");
  }
  if (Single!(Long) == type) {
    return buildFunCall(fastcast!(Function)~ sysmod.lookup("ltoa"), ex, "ltoa");
  }
  if (Single!(Float) == type) {
    return buildFunCall(fastcast!(Function)~ sysmod.lookup("ftoa"), ex, "ftoa");
  }
  if (Single!(Double) == type) {
    return buildFunCall(fastcast!(Function)~ sysmod.lookup("dtoa"), ex, "dtoa");
  }
  if (auto p = fastcast!(Pointer)~ type) {
    return buildFunCall(fastcast!(Function)~ sysmod.lookup("ptoa"), reinterpret_cast(voidp, ex), "ptoa");
  }
  if (auto sa = fastcast!(StaticArray)~ type) {
    if (fastcast!(CValue)~ ex) {
      ex = staticToArray(ex);
      type = ex.valueType();
    }
  }
  if (auto dg = fastcast!(Delegate)~ type) {
    return iparse!(Expr, "gen_dg_format", "tree.expr")
      (`"dg(fun $(void*:dg.fun), data $(void*:dg.data))"`,
        "dg", ex
      );
  }
  if (auto tup = fastcast!(Tuple)~ type) {
    auto res = new ConcatChain(new StringExpr("{")); // put here for type
    return new CallbackExpr(res.valueType(), ex, res /apply/ (ConcatChain res, Expr ex, AsmFile af) {
      Expr build(LValue lv) {
        foreach (i, entry; getTupleEntries(lv)) {
          if (i) res.addArray(new StringExpr(", "));
          res.addArray(iparse!(Expr, "!safecode_gen_tuple_member_format", "tree.expr.literal.stringex")(`"$entry"`, "entry", entry));
        }
        res.addArray(new StringExpr("}"));
        return res;
      }
      if (auto lv = fastcast!(LValue)~ ex) build(lv).emitAsm(af);
      else mkVar(af, res.valueType(), true, (Variable outer) {
        mkVar(af, ex.valueType(), true, (Variable var) {
          (new Assignment(var, ex)).emitAsm(af);
          (new Assignment(outer, build(var))).emitAsm(af);
        });
        af.sfree(ex.valueType().size); // cheat
      });
    });
  }
  auto ar = fastcast!(Array)~ type;
  auto ea = fastcast!(ExtArray)~ type;
  if (ar || ea) {
    IType et;
    if (ar) et = ar.elemType;
    if (ea) et = ea.elemType;
    if (Single!(Char) == et) {
      return ex;
    }
    // logln("et is ", et);
    return new CallbackExpr(Single!(Array, Single!(Char)), ex, (Expr ex, AsmFile af) {
      mkVar(af, Single!(Array, Single!(Char)), true, (Variable var) {
        iparse!(Scope, "!safecode_gen_array_format", "tree.scope")
        (`{
            char[auto ~] res;
            res = res ~ "[";
            auto ar = array;
            for (int i = 0; i < ar.length; ++i) {
              if i res = res ~ ", ";
              auto elem = ar[i];
              res = res ~ "$elem";
            }
            res = res ~ "]";
            var = res[];
          }`,
          namespace(),
          "var", var, "array", ex,
          af
        ).emitAsm(af);
      });
    });
  }
  auto obj = fastcast!(IType) (sysmod.lookup("Object"));
  if (gotImplicitCast(ex, obj, (IType it) { return test(it == obj); })) {
    return iparse!(Expr, "gen_obj_toString_call", "tree.expr")
                  (`obj.toString()`, "obj", lvize(ex));
  }
  return null;
}
