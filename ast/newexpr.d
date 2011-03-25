module ast.newexpr;

import
  ast.oop, ast.base, ast.static_arrays, ast.namespace, ast.parse,
  ast.vardecl, ast.int_literal, ast.pointer, ast.structure: doAlign;

Object gotNewClassExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  IType classtype;
  if (!rest(t2, "type", &classtype)) return null;
  auto cr = fastcast!(ClassRef) (resolveType(classtype));
  if (!cr) return null;
  
  Expr initParam;
  rest(t2, "tree.expr _tree.expr.arith", &initParam);
  
  text = t2;
  return new CallbackExpr(cr, initParam, stuple(text, cr)
  /apply/ (string text, ClassRef cr, Expr initParam, AsmFile af)
  {
    mixin(mustOffset("nativePtrSize"));
    mkVar(af, cr, true, (Variable var) {
      mixin(mustOffset("0"));
      iparse!(Statement, "new_class", "tree.stmt")
      (`{
          var = type-of var: mem.calloc(size, 1);
          (void**:var)[0] = _classinfo;
        }`,
        "var", var,
        "size", mkInt(cr.myClass.size),
        "_classinfo", new Symbol(cr.myClass.ci_name())
      ).emitAsm(af);
      
      void initClass(Class cl) {
        if (cl.parent) initClass(cl.parent);
        auto base = cl.mainSize();
        doAlign(base, voidp);
        base /= 4;
        int id = 0;
        void iterLeaves(void delegate(Intf, int) dg) {
          void recurse(Intf intf, int myOffs) {
            if (intf.parents.length) foreach (i, intf2; intf.parents) {
              recurse(intf2, myOffs);
              myOffs += intf2.clsize();
            }
            else dg(intf, myOffs);
          }
          auto offs = cl.ownClassinfoLength;
          foreach (i, intf; cl.iparents) {
            recurse(intf, offs);
            offs += intf.clsize();
          }
        }
        iterLeaves((Intf intf, int offs) {
          // logln("init [", base, " + ", id, "] with intf ", intf.name, "; offs ", offs);
          iparse!(Statement, "init_intfs", "tree.semicol_stmt.assign")
          (`(void**:var)[base + id] = (void**:_classinfo + offs)`,
            "var", var,
            "base", mkInt(base), "id", mkInt(id++),
            "_classinfo", new Symbol(cr.myClass.ci_name()),
            "offs", mkInt(offs)
          ).emitAsm(af);
        });
      }
      initClass(cr.myClass);
      try {
        if (initParam) {
          (new ExprStatement(
            iparse!(Expr, "call_constructor", "tree.expr _tree.expr.arith")
                  (`var.init ex`,
                    "var", var, "ex", initParam)
          )).emitAsm(af);
        }
        else if (cr.myClass.lookupRel("init", var)) {
          (new ExprStatement(
            iparse!(Expr, "call_constructor_void", "tree.expr _tree.expr.arith")
                   (`var.init()`,
                    "var", var)
          )).emitAsm(af);
        }
      } catch (Exception ex) {
        text.failparse(ex);
      }
    });
  });
}
mixin DefaultParser!(gotNewClassExpr, "tree.expr.new.class", "125", "new");

import ast.casting, ast.slice: mkPointerSlice;
Object gotNewArrayExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  IType ty;
  if (!rest(t2, "type", &ty))
    return null;
  
  if (auto sa = fastcast!(StaticArray)~ ty) {
    IType base = sa.elemType;
    Expr len = mkInt(sa.length);
    auto t3 = t2;
    Expr newlen;
    if (t3.accept("[") &&
        rest(t3, "tree.expr", &newlen) &&
        gotImplicitCast(newlen, (IType it) { return !!fastcast!(SysInt) (it); }) &&
        t3.accept("]")) {
      t2 = t3;
      len = newlen;
      base = sa;
    }
    text = t2;
    // logln("new1 ", base, " [", len, "]");
    return fastcast!(Object)~
      mkPointerSlice(
        reinterpret_cast(
          new Pointer(base),
          iparse!(Expr, "do_calloc", "tree.expr")
                ("mem.calloc(len, basesz)",
                  "len", len, "basesz", mkInt(base.size))),
        mkInt(0), len);
  } else {
    Expr len;
    if (!t2.accept("[") ||
        !rest(t2, "tree.expr", &len) ||
        !gotImplicitCast(len, (IType it) { return !!fastcast!(SysInt) (it); }) ||
        !t2.accept("]"))
      return null;
    text = t2;
    // logln("new2 ", ty, " [", len, "]");
    return fastcast!(Object)~
      mkPointerSlice(
        reinterpret_cast(new Pointer(ty),
          iparse!(Expr, "new_dynamic_array", "tree.expr")
                 ("mem.calloc(len, size-of ty)", "len", len, "ty", ty)
        ),
        mkInt(0), len
      );
  }
}
mixin DefaultParser!(gotNewArrayExpr, "tree.expr.new.array", "12", "new");

import ast.nestfun, ast.opers, ast.dg, ast.arrays, ast.fun;
Object gotNewDelegateExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.arith", &ex))
    return null;
  
  auto re = fastcast!(NestFunRefExpr) (ex);
  if (!re) return null;
  
  text = t2;
  
  auto nf = re.fun.context.get!(Function);
  auto start = nf.framestart(), end = re.fun.context.frame_end();
  // NOTE: end is smaller.
  auto size = start - end; // lol
  auto framestartp = lookupOp("+", reinterpret_cast(voidp, re.base), mkInt(end));
  auto array = mkPointerSlice(framestartp, mkInt(0), mkInt(size));
  auto array2p = getArrayPtr(iparse!(Expr, "dup_dg", "tree.expr")(`fastdupv array`, "array", array));
  auto base2 = lookupOp("+", array2p, mkInt(-end));
  return new DgConstructExpr(re.fun.getPointer(), base2);
}
mixin DefaultParser!(gotNewDelegateExpr, "tree.expr.new.dg", "13", "new");

Object gotNewValueExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  IType ty;
  if (!rest(t2, "type", &ty))
    t2.failparse("Malformed value-new");
  
  text = t2;
  
  return fastcast!(Object)~ iparse!(Expr, "new_value", "tree.expr")
    ("type*:mem.calloc(1, size-of type)",
     "type", ty
    );
}
mixin DefaultParser!(gotNewValueExpr, "tree.expr.new.value", "2", "new");

static this() { parsecon.addPrecedence("tree.expr.new", /*"20"*/"24015"); }
