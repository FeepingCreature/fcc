module ast.newexpr;

import
  ast.oop, ast.base, ast.static_arrays, ast.namespace, ast.parse,
  ast.vardecl, ast.int_literal, ast.pointer, ast.assign, ast.fold,
  ast.funcall, ast.modules, ast.tuples, ast.structure: doAlign;

Object gotNewClassExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  Object obj;
  if (!rest(t2, "type"[], &obj)) { return null; }
  auto it = fastcast!(IType) (obj);
  if (!it) return null;
  auto cr = fastcast!(ClassRef) (resolveType(it));
  if (!cr) {
    auto ir = fastcast!(IntfRef) (resolveType(it));
    if (ir) t2.failparse("Cannot new an interface! "[]);
    return null;
  }
  
  Expr initParam;
  rest(t2, "tree.expr _tree.expr.arith"[], &initParam);
  
  if (cr && cr.myClass.isabstract())
    text.failparse("cannot instantiate abstract class"[]);
  
  text = t2;
  Expr protConstCall;
  PlaceholderTokenLV var_token;
  if (initParam) {
    New(var_token, it, "early constructor call"[]);
    protConstCall =
      iparse!(Expr, "call_constructor_early"[], "tree.expr _tree.expr.arith"[])
              (`var.init ex`, namespace(),
              "var"[], var_token, "ex"[], initParam);
  }
  return fastalloc!(CallbackExpr)(Format("class-new "[], cr), cr, protConstCall, stuple(text, cr, var_token)
  /apply/ (string text, ClassRef cr, PlaceholderTokenLV var_token, Expr protConstCall, AsmFile af)
  {
    mixin(mustOffset("nativePtrSize"[]));
    af.comment("mk var"[]);
    mkVar(af, cr, true, (Variable var) {
      af.comment("new_class"[]);
      mixin(mustOffset("0"[]));
      iparse!(Statement, "new_class"[], "tree.stmt"[])
      (`var = type-of var: mem.calloc(size, 1);`,
        "var"[], var,
        "size"[], mkInt(cr.myClass.size)
      ).emitAsm(af);
      // (void**:var)[0] = _classinfo;
      (fastalloc!(Assignment)(
        fastcast!(LValue) (lookupOp("index"[],
          reinterpret_cast(voidpp, var),
          mkInt(0))),
        reinterpret_cast(voidp, fastalloc!(Symbol)(cr.myClass.ci_name()))
      )).emitAsm(af);
      
      if (cr.myClass.ctx) {
        auto transformed = cr.myClass.ctx.transform(
          fastalloc!(DerefExpr)(reinterpret_cast(fastalloc!(Pointer)(cr.myClass.data), var))
        );
        Expr bp;
        if (Single!(Pointer, Single!(Void)) == cr.myClass.rtpt)
          bp = reinterpret_cast(Single!(Pointer, Single!(Void)), Single!(Register!("ebp"[])));
        else
          bp = fastcast!(Expr) (namespace().lookup("__base_ptr"[]));
        if (!bp) {
          logln("no base ptr found in "[], namespace());
          fail;
        }
        // logln("transformed: "[], transformed);
        // logln("baseptr: "[], bp);
        (fastalloc!(Assignment)(fastcast!(LValue) (transformed), bp)).emitAsm(af);
      }
      void initClass(Class cl) {
        if (cl.parent) initClass(cl.parent);
        auto base = cl.classSize(false);
        doAlign(base, voidp);
        base /= 4;
        int id = 0;
        void iterLeaves(void delegate(Intf, Expr) dg) {
          void recurse(Intf intf, Expr myOffs) {
            if (intf.parents.length) foreach (i, intf2; intf.parents) {
              recurse(intf2, myOffs);
              myOffs = foldex(lookupOp("+"[], myOffs, mkInt(intf2.clsize())));
            }
            else dg(intf, myOffs);
          }
          auto offs = cl.ownClassinfoLength;
          foreach (i, intf; cl.iparents) {
            recurse(intf, offs);
            offs = foldex(lookupOp("+"[], offs, mkInt(intf.clsize())));
          }
        }
        iterLeaves((Intf intf, Expr offs) {
          // logln("init ["[], base, " + "[], id, "] with intf "[], intf.name, "; offs "[], offs);
          /*iparse!(Statement, "init_intfs"[], "tree.semicol_stmt.assign"[])
          (`(void**:var)[base + id] = (void**:_classinfo + offs)`,
            "var"[], var,
            "base"[], mkInt(base), "id"[], mkInt(id++),
            "_classinfo"[], fastalloc!(Symbol)(cr.myClass.ci_name()),
            "offs"[], offs
          ).emitAsm(af);*/
          auto slot = fastcast!(LValue) (lookupOp("index"[],
            reinterpret_cast(voidpp, var),
            mkInt(base + (id ++))
          ));
          auto classinfo_reference = reinterpret_cast(voidp, lookupOp("+"[],
            reinterpret_cast(voidpp, fastalloc!(Symbol)(cr.myClass.ci_name())),
            offs
          ));
          (fastalloc!(Assignment)(slot, classinfo_reference)).emitAsm(af);
        });
      }
      initClass(cr.myClass);
      try {
        if (protConstCall) {
          void subst(ref Iterable it) {
            if (it is var_token) it = var;
            else it.iterate(&subst);
          }
          protConstCall.iterate(&subst);
          (fastalloc!(ExprStatement)(foldex(protConstCall))).emitAsm(af);
        } else if (cr.myClass.lookupRel("init"[], var)) {
          (fastalloc!(ExprStatement)(foldex(
            iparse!(Expr, "call_constructor_void"[], "tree.expr _tree.expr.arith"[])
                    (`var.init()`, namespace(),
                    "var"[], var)
          ))).emitAsm(af);
        }
      } catch (Exception ex) {
        text.failparse(ex);
      }
    });
  });
}
mixin DefaultParser!(gotNewClassExpr, "tree.expr.new.class"[], "125"[], "new"[]);

import ast.casting, ast.slice: mkPointerSlice;
Object gotNewArrayExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  IType base;
  if (!rest(t2, "type"[], &base))
    return null;
  
  auto arr = fastcast!(Array) (base), ea = fastcast!(ExtArray) (base);
  if (!arr && !ea) return null;
  Expr len;
  if (!rest(t2, "tree.expr _tree.expr.arith.concat"[], &len))
    t2.failparse("Expected length for array-new"[]);
  auto backuplen = len;
  if (!gotImplicitCast(len, (IType it) { return !!fastcast!(SysInt) (it); }))
    t2.failparse("Index is a "[], backuplen.valueType(), "[], not an int! "[]);
  text = t2;
  // logln("new1 "[], base, " ["[], len, "]"[]);
  Expr allocedPtr;
  IType et;
  if (arr) et = arr.elemType;
  else et = ea.elemType;
  auto mem = fastcast!(Expr) (sysmod.lookup("mem"[]));
  if (et.isPointerLess()) {
    allocedPtr = buildFunCall(
      fastcast!(Function) (
        fastcast!(RelNamespace) (mem.valueType()).lookupRel("calloc_atomic"[], mem)
      ),
      lookupOp("*"[], len, mkInt(et.size)),
      "calloc_atomic for new array"[]);
  } else {
    allocedPtr = buildFunCall(
      fastcast!(Function) (
        fastcast!(RelNamespace)(mem.valueType()).lookupRel("calloc"[], mem)
      ),
      mkTupleExpr(len, mkInt(et.size)),
      "calloc for new array"[]);
  }
  Expr res = mkPointerSlice(
    reinterpret_cast(
      fastalloc!(Pointer)(et),
      allocedPtr
    ),
    mkInt(0), len
  );
  if (arr) return fastcast!(Object) (res);
  else {
    auto ea2 = fastalloc!(ExtArray)(ea.elemType, false);
    if (!gotImplicitCast(res, (IType it) { return test(it == ea2); }))
      text.failparse("Could not convert to correct array type"[]);
    return fastcast!(Object) (reinterpret_cast(ea, res));
  }
}
mixin DefaultParser!(gotNewArrayExpr, "tree.expr.new.array"[], "12"[], "new"[]);

import ast.nestfun, ast.opers, ast.dg, ast.arrays, ast.fun, ast.scopes;
Object gotNewDelegateExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.arith"[], &ex))
    return null;
  
  auto re = fastcast!(NestFunRefExpr) (ex);
  if (!re) return null;
  
  text = t2;
  
  auto nf = re.fun.context.get!(Function);
  auto start = nf.framestart(), end = (fastcast!(Scope) (re.fun.context)).frame_end();
  // logln("frame range for dg allocation: "[], start, " .. "[], end, " for "[], re.fun.name);
  // NOTE: end is smaller.
  auto size = start - end; // lol
  auto framestartp = lookupOp("+"[], reinterpret_cast(voidp, re.base), mkInt(end));
  auto array = mkPointerSlice(framestartp, mkInt(0), mkInt(size));
  auto array2p = getArrayPtr(buildFunCall(
    fastcast!(Function) (sysmod.lookup("fastdupv"[])),
    array, "new dg fastdupv call"[]));
  auto base2 = lookupOp("+"[], array2p, mkInt(-end));
  return fastalloc!(DgConstructExpr)(re.fun.getPointer(), base2);
}
mixin DefaultParser!(gotNewDelegateExpr, "tree.expr.new.dg"[], "13"[], "new"[]);

Object gotNewValueExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  
  IType ty;
  if (!rest(t2, "type"[], &ty))
    t2.failparse("Malformed value-new"[]);
  
  text = t2;
  
  return fastcast!(Object)~ iparse!(Expr, "new_value"[], "tree.expr"[])
    ("type*:mem.calloc(1, size-of type)"[],
     "type"[], ty
    );
}
mixin DefaultParser!(gotNewValueExpr, "tree.expr.new.value"[], "2"[], "new"[]);

static this() { parsecon.addPrecedence("tree.expr.new"[], /*"20"*/"24015"[]); }
