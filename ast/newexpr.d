module ast.newexpr;

import
  ast.oop, ast.base, ast.static_arrays, ast.namespace, ast.parse,
  ast.vardecl, ast.int_literal, ast.pointer, ast.assign, ast.fold,
  ast.funcall, ast.modules, ast.tuples, ast.literals;

Object gotNewClassExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (t2.accept("-")) return null; // new-foo
  
  Object obj;
  if (!rest(t2, "type"[], &obj)) {
    string id;
    auto t3 = t2;
    if (t2.gotIdentifier(id, true) && !namespace().lookup(id) && id != "delegate") {
      unknownId(id, t2, true);
    }
    return null;
  }
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
    text.failparse("cannot instantiate abstract class: unimplemented ", cr.myClass.getAbstractFuns());
  
  text = t2;
  Expr protConstCall;
  PlaceholderTokenLV res_token;
  New(res_token, it, "early constructor call"[]);
  try {
    if (initParam) {
      protConstCall =
        iparse!(Expr, "call_constructor_early", "tree.expr _tree.expr.arith")
               (`res.init ex`, namespace(),
                "res"[], res_token, "ex"[], initParam);
    } else if (cr.myClass.lookupRel("init", res_token)) {
      protConstCall =
        iparse!(Expr, "call_constructor_early_void", "tree.expr _tree.expr.arith")
               (`res.init()`, namespace(),
                "res"[], res_token);
    }
  } catch (Exception ex) {
    text.failparse(ex);
  }
  return fastalloc!(CallbackExpr)(Format("class-new "[], cr), cr, protConstCall, stuple(text, cr, res_token)
  /apply/ (string text, ClassRef cr, PlaceholderTokenLV res_token, Expr protConstCall, LLVMFile lf)
  {
    mixin(mustOffset("1"));
    auto res = fastalloc!(LLVMRef)(cr);
    res.allocate(lf);
    res.begin(lf);
    scope(success) {
      res.emitLLVM(lf);
      res.end(lf);
    }
    
    mixin(mustOffset("0"));
    iparse!(Statement, "new_class"[], "tree.stmt"[])
    (`res = type-of res: mem.calloc(size, 1);`,
      "res"[], res,
      "size"[], llvmval(cr.myClass.llvmSize())
    ).emitLLVM(lf);
    // (void**:res)[0] = _classinfo;
    (fastalloc!(Assignment)(
      fastcast!(LValue) (lookupOp("index"[],
        reinterpret_cast(voidpp, res),
        mkInt(0))),
      fastalloc!(Symbol)(cr.myClass.vt_name(), Single!(Void))
    )).emitLLVM(lf);
    
    if (cr.myClass.ctx) {
      auto transformed = cr.myClass.ctx.transform(
        fastalloc!(DerefExpr)(reinterpret_cast(fastalloc!(Pointer)(cr.myClass.data), res))
      );
      Expr bp;
      if (Single!(Pointer, Single!(Void)) == cr.myClass.rtpt)
        bp = fastalloc!(LLVMValue)("%__stackframe", Single!(Pointer, Single!(Void)));
      else
        bp = fastcast!(Expr) (namespace().lookup("__base_ptr"[]));
      if (!bp) {
        logln("no base ptr found in "[], namespace());
        fail;
      }
      auto tt = fastcast!(Expr) (transformed).valueType();
      auto bt = bp.valueType();
      if (!gotImplicitCast(bp, (IType it) { return !!(it == tt); })) {
        text.failparse("Could not convert class context into appropriate"
        "  allocation context for subclass: ", bt, " does not cast to ", tt);
      }
      // logln("transformed: "[], transformed);
      // logln("baseptr: "[], bp);
      emitAssign(lf, fastcast!(LValue) (transformed), bp);
    }
    void initClass(Class cl) {
      if (cl.parent) initClass(cl.parent);
      // auto base = cl.classSize(false);
      auto base = cl.offsetOfVTable();
      base = lldiv(base, "4");
      int id = 0;
      void iterLeaves(void delegate(Intf, Expr) dg) {
        void recurse(Intf intf, LazyDeltaInt myOffs) {
          auto backup = myOffs.delta;
          scope(success) myOffs.delta = backup;
          
          if (intf.parents.length) foreach (i, intf2; intf.parents) {
            recurse(intf2, myOffs);
            myOffs.delta += intf2.clsize();
          }
          else dg(intf, myOffs);
        }
        auto offs = cl.ownClassinfoLength;
        foreach (i, intf; cl.iparents) {
          recurse(intf, offs);
          offs.delta += intf.clsize();
        }
      }
      iterLeaves((Intf intf, Expr offs) {
        // logln(cl.name, ": init ["[], base, " + "[], id, "] with intf "[], intf.name, "; offs "[], offs);
        /*iparse!(Statement, "init_intfs"[], "tree.semicol_stmt.assign"[])
        (`(void**:var)[base + id] = (void**:_classinfo + offs)`,
          "var"[], var,
          "base"[], mkInt(base), "id"[], mkInt(id++),
          "_classinfo"[], fastalloc!(Symbol)(cr.myClass.vt_name()),
          "offs"[], offs
        ).emitLLVM(lf);*/
        auto slot = fastcast!(LValue) (lookupOp("index"[],
          reinterpret_cast(voidpp, res),
          llvmval(lladd(base, qformat(id++)))
        ));
        auto classinfo_reference = reinterpret_cast(voidp, lookupOp("+"[],
          reinterpret_cast(voidpp, fastalloc!(Symbol)(cr.myClass.vt_name(), Single!(Void))),
          offs
        ));
        emitAssign(lf, slot, classinfo_reference);
        // auto printf = sysmod.lookup("printf");
        // buildFunCall(printf, mkString(qformat("struct info = ", cl.data.llvmType(), " for ", cl.data, " and offs at ", cl.name, " ", cl.offsetOfVTable(), "+", id-1, "\n")), "printf").emitLLVM(lf); lf.pop();
        // buildFunCall(printf, mkTupleExpr(mkString("classinfo for "~intf.name~" written to %p\n"), fastalloc!(RefExpr)(slot)), "printf").emitLLVM(lf); lf.pop();
      });
    }
    initClass(cr.myClass);
    // assert(!!protConstCall);
    void subst(ref Iterable it) {
      if (it is res_token) it = res;
      else it.iterate(&subst);
    }
    if (protConstCall) {
      protConstCall = protConstCall.dup;
      protConstCall.iterate(&subst);
      (fastalloc!(ExprStatement)(protConstCall)).emitLLVM(lf);
    }
  });
}
mixin DefaultParser!(gotNewClassExpr, "tree.expr.new.class"[], "125"[], "new"[]);

import ast.casting, ast.slice: mkPointerSlice;
Object gotNewArrayExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (t2.accept("-")) return null; // new-bar
  
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
  Expr res = tmpize_maybe(len, delegate Expr(Expr len) {
    Expr allocedPtr;
    IType et;
    if (arr) et = arr.elemType;
    else et = ea.elemType;
    auto mem = fastcast!(Expr) (sysmod.lookup("mem"[]));
    if (et.isPointerLess()) {
      allocedPtr = buildFunCall(
        fastcast!(RelNamespace) (mem.valueType()).lookupRel("calloc_atomic"[], mem),
        lookupOp("*"[], len, llvmval(et.llvmSize())),
        "calloc_atomic for new array"[]);
    } else {
      allocedPtr = buildFunCall(
        fastcast!(RelNamespace)(mem.valueType()).lookupRel("calloc"[], mem),
        mkTupleExpr(len, llvmval(et.llvmSize())),
        "calloc for new array"[]);
    }
    return mkPointerSlice(
      reinterpret_cast(
        fastalloc!(Pointer)(et),
        allocedPtr
      ),
      mkInt(0), len
    );
  });
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
  if (t2.accept("-")) return null; // new-baz
  Expr ex;
  if (!rest(t2, "tree.expr _tree.expr.arith"[], &ex))
    return null;
  
  auto re = fastcast!(NestFunRefExpr) (ex);
  if (!re) return null;
  if (!re.fun.type.ret) {
    re.fun.parseMe;
    if (!re.fun.type.ret) {
      logln("wat: ", re);
      logln("::", !!re.fun.coarseSrc, " ", re.fun.inFixup);
      fail;
    }
  }
  
  text = t2;
  
  auto nf = re.fun.context.get!(Function);
  auto frame = frametype2(re.fun.context.get!(ScopeLike)), size = lltypesize(frame);
  // logln("frame range for dg allocation: "[], size, " for ", frame, " of ", re.fun.name);
  auto framestartp = reinterpret_cast(voidp, re.base);
  auto array = mkPointerSlice(framestartp, mkInt(0), llvmval(size));
  auto array2p = getArrayPtr(buildFunCall(
    sysmod.lookup("fastdupv"[]),
    array, "new dg fastdupv call"[]));
  return fastalloc!(DgConstructExpr)(re.fun.getPointer(), array2p);
}
mixin DefaultParser!(gotNewDelegateExpr, "tree.expr.new.dg"[], "13"[], "new"[]);

Object gotNewValueExpr(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (t2.accept("-")) return null; // new-whee
  
  IType ty;
  if (!rest(t2, "type"[], &ty))
    t2.failparse("Malformed value-new"[]);
  
  text = t2;
  
  return fastcast!(Object)~ reinterpret_cast(new Pointer(ty), iparse!(Expr, "new_value"[], "tree.expr"[])
    ("mem.calloc(1, size-of type)"[],
     "type"[], ty
    ));
}
mixin DefaultParser!(gotNewValueExpr, "tree.expr.new.value"[], "2"[], "new"[]);

static this() { addPrecedence("tree.expr.new"[], /*"20"*/"24015"[]); }
