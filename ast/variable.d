module ast.variable;

import ast.base, ast.opers, ast.literals, parseBase, ast.casting, ast.static_arrays;

import dwarf2, tools.log;
class Variable : LValue, Named {
  string address() { return Format(baseOffset, "(%ebp)"[]); }
  override {
    void emitAsm(AsmFile af) {
      mixin(mustOffset("type.size"[]));
      if (isARM) {
        if (type.size == 4) {
          af.mmove4(qformat("[fp, #"[], baseOffset, "]"[]), "r0"[]);
          af.pushStack("r0"[], 4);
        } else {
          armpush(af, "fp"[], type.size, baseOffset);
        }
      } else {
        af.pushStack(address, type.size);
      }
    }
    void emitLocation(AsmFile af) {
      if (isARM) {
        lookupOp("+"[], new Register!("ebp"[]), mkInt(baseOffset)).emitAsm(af);
      } else {
        af.loadAddress(qformat(baseOffset, "(%ebp)"), "%eax");
        af.pushStack("%eax", nativePtrSize);
      }
      
    }
    IType valueType() {
      return type;
    }
  }
  IType type;
  string name;
  // offset off ebp
  int baseOffset;
  bool dontInit;
  Expr initval;
  static Stuple!(Expr, IType)[] initval_cache;
  void initInit() {
    if (initval) return;
    else {
      auto vt = valueType();
      synchronized {
        foreach (ref entry; initval_cache)
          if (entry._1 == vt) {
            initval = entry._0;
            return;
          }
        initval = reinterpret_cast(
          vt,
          fastalloc!(DataExpr)(type.initval())
        );
        initval_cache ~= stuple(initval, vt);
      }
    }
  }
  this() { }
  this(IType t, string s, int i) {
    type = t;
    name = s;
    baseOffset = i;
    initInit();
  }
  this(IType t, string s, Expr ex, int i) {
    this(t, s, i);
    initval = ex;
  }
  override string getIdentifier() { return name; }
  mixin DefaultDup!();
  mixin defaultIterate!();
  string toString() {
    if (name) return name;
    return Format("[ var of "[], type, " at "[], baseOffset, "]"[]);
  }
  void registerDwarf2(Dwarf2Controller dwarf2) {
    if (name && !name.startsWith("__temp"[])) {
      auto ty = resolveType(type);
      auto dw2t = fastcast!(Dwarf2Encodable) (ty);
      if (!dw2t || !dw2t.canEncode) {
        // fallback
        dw2t = fastalloc!(StaticArray)(Single!(Byte), ty.size());
      }
      auto typeref = registerType(dwarf2, dw2t);
      auto varinfo = fastalloc!(Dwarf2Section)(dwarf2.cache.getKeyFor("variable"[]));
      with (varinfo) {
        data ~= dwarf2.strings.addString(name);
        data ~= typeref;
        data ~= ".byte\t2f-1f\t/* fbreg, offset */";
        data ~= "1:";
        data ~= qformat(".byte\t"[], hex(DW.OP_fbreg), "\t/* fbreg */"[]);
        data ~= qformat(".sleb128\t"[], baseOffset, "\t/* base offset */"[]);
        data ~= "2:";
      }
      dwarf2.add(varinfo);
    }
  }
}
