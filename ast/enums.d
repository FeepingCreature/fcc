module ast.enums;

import parseBase;
import
  ast.base, ast.types, ast.namespace, ast.casting, ast.literals,
  ast.math, ast.opers, ast.fold, ast.fun, ast.arrays, ast.modules,
  ast.prefixfun;

class Enum : Namespace, RelNamespace, IType, Named, ExprLikeThingy {
  string name;
  IType base;
  this(string n, IType b) {
    name = n;
    base = b;
    sup = namespace();
  }
  // members
  string[] names;
  Expr[] values;
  void addEntry(string s, Expr e) { names ~= s; values ~= e; }
  string getParseFunName() {
    return mangle() ~ "_parse_fun";
  }
  string getToStringFunName() {
    return mangle() ~ "_to_string";
  }
  string getIsDefinedFunName() {
    return mangle() ~ "_is_defined";
  }
  override {
    string getIdentifier() { return name; }
    string mangle() { return sup.mangle(null, null)~"_enum_"~name; }
    bool isPointerLess() { return base.isPointerLess(); }
    bool isComplete() { return true; }
    string llvmType() { return base.llvmType(); }
    string llvmSize() { return base.llvmSize(); }
    mixin TypeDefaults!(true);
    Object lookupRel(string name, Expr base, bool isDirectLookup = true) {
      if (base && name == "toString") {
        auto res = fastcast!(Function) (sup.lookup(getToStringFunName()));
        if (!res) return null; // huh
        return fastalloc!(PrefixFunction)(base, res);
      }
      return null;
    }
    bool isTempNamespace() { return true; }
    Object lookup(string name, bool local = false) {
      if (name == "parse") {
        return sup.lookup(getParseFunName());
      }
      if (name == "toString") {
        return sup.lookup(getToStringFunName());
      }
      if (name == "isDefined") {
        return sup.lookup(getIsDefinedFunName());
      }
      foreach (i, n; names)
        if (n == name)
          return fastcast!(Object) (reinterpret_cast(this, values[i]));
      if (!local) if (auto res = sup.lookup(name, local)) return res;
      if (local) throw new Exception("no such enum member");
      return null;
    }
    string mangle(string name, IType type) {
      fail; // what are you DOING
      return null;
    }
  }
}

import ast.int_literal;

Object gotEnum(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string name;
  if (!t2.gotIdentifier(name))
    t2.failparse("Enum name expected! "[]);
  IType base = Single!(SysInt);
  if (t2.accept(":"[])) {
    if (!rest(t2, "type"[], &base))
      t2.failparse("Expected enum base type! "[]);
  }
  if (!t2.accept("{"[]))
    t2.failparse("Expected opening bracket for enum. "[]);
  auto en = fastalloc!(Enum)(name, base);
  
  auto backup = namespace();
  namespace.set(en);
  scope(exit) namespace.set(backup);
  
  Expr val, one;
  if (Single!(Short) == base) {
    val = fastalloc!(IntLiteralAsShort)(mkInt(0));
    one = fastalloc!(IntLiteralAsShort)(mkInt(1));
  } else if (Single!(Byte) == base) {
    val = fastalloc!(ShortAsByte)(fastalloc!(IntLiteralAsShort)(mkInt(0)));
    one = fastalloc!(ShortAsByte)(fastalloc!(IntLiteralAsShort)(mkInt(1)));
  } else {
    val = mkInt(-1); // base-zero!
    one = mkInt(1);
  }
  
grabIdentifier:
  string idname;
  if (!t2.gotIdentifier(idname))
    t2.failparse("Expected enum member identifier"[]);
  if (t2.accept("="[])) {
    if (!rest(t2, "tree.expr"[], &val))
      t2.failparse("Expected enum value expr"[]);
    auto backupval = val;
    if (!gotImplicitCast(val, (IType it) { return test(it == base); }))
      t2.failparse("Enum value of "[], backupval.valueType(), " did not match "[],
                    base);
  } else {
    val = collapse(lookupOp("+"[], val, one));
  }
  en.addEntry(idname, val);
  if (t2.accept(","[])) goto grabIdentifier;
  // end goto
  if (!t2.accept("}"[]))
    t2.failparse("Expected closing bracket"[]);
  text = t2;
  en.sup.add(en);
  
  void deffun(string name, IType ret, Argument arg, void delegate(Function) dg) {
    auto fun = new Function;
    New(fun.type);
    fun.type.ret = ret;
    fun.type.params ~= arg;
    fun.name = name;
    fun.fixup;
    en.sup.add(fun);
    current_module().addEntry(fun);
    auto backup2 = namespace();
    scope(exit) namespace.set(backup2);
    namespace.set(fun);
    dg(fun);
  }
  // TODO: optimize by detecting runs
  deffun(en.getParseFunName(), en, Argument(Single!(Array, Single!(Char)), "name"),
    (Function fun) {
      foreach (i, str; en.names) {
        fun.addStatement(
          iparse!(Statement, "enum_parse_branch"[], "tree.stmt"[])
                 (`if (name == str) return enum: ex; `, fun,
                  "str"[], mkString(str), "ex"[], en.values[i],
                  "enum"[], en)
        );
      }
      fun.addStatement(
        iparse!(Statement, "enum_fail_branch"[], "tree.stmt"[])
               (`raise new Error "No such enum value in $myname: '$name'"; `, fun,
                "myname"[], mkString(name))
      );
    }
  );
  deffun(en.getIsDefinedFunName(), fastcast!(IType) (sysmod.lookup("bool")), Argument(en.base, "arg"),
    (Function fun) {
      foreach (i, str; en.names) {
        fun.addStatement(
          iparse!(Statement, "enum_isdefined_branch"[], "tree.stmt"[])
                 (`if (arg == ex) return true; `, fun,
                  "ex"[], en.values[i])
        );
      }
      fun.addStatement(
        iparse!(Statement, "enum_isdefined_fail"[], "tree.stmt"[])
               (`return false; `, fun)
      );
    }
  );
  deffun(en.getToStringFunName(), Single!(Array, Single!(Char)), Argument(en, "value"),
    (Function fun) {
      foreach (i, str; en.names) {
        fun.addStatement(
          iparse!(Statement, "enum_tostring_branch"[], "tree.stmt"[])
                 (`if (value == ex) return str; `, fun,
                  "str"[], mkString(str), "ex"[], en.values[i])
        );
      }
      fun.addStatement(
        iparse!(Statement, "enum_tostring_fail_branch"[], "tree.stmt"[])
               (`raise new Error "Invalid enum value for $myname: $value"; `, fun,
                "myname"[], mkString(name))
      );
    }
  );
  
  return Single!(NoOp);
}
mixin DefaultParser!(gotEnum, "tree.toplevel.enum"[], null, "enum"[]);
mixin DefaultParser!(gotEnum, "tree.stmt.enum"[], "313"[], "enum"[]);

// enums cast implicitly to their base type
// this can be useful when wrapping APIs
// that define enum members in relation to other members
// ie. A = 5, B = A + 4
static this() {
  implicits ~= delegate Expr(Expr ex) {
    auto vt = ex.valueType();
    auto en = fastcast!(Enum) (vt);
    if (!en) return null;
    if (auto lv = fastcast!(LValue) (ex))
      return fastalloc!(RCC)(en.base, lv);
    return reinterpret_cast(en.base, ex);
  };
}
