module ast.variable;

import ast.base, ast.opers, ast.literals, parseBase, ast.casting, ast.static_arrays, ast.namespace;

import dwarf2, tools.log;
class Variable : LValue, Named {
  string address() {
    todo("Variable::address");
    return null;
    // return Format(baseOffset, "(%ebp)"[]);
  }
  override {
    void emitLLVM(LLVMFile lf) {
      if (!stacktype) fail;
      auto stackp = bitcastptr(lf, "i8", stacktype, "%__stackframe");
      auto varp = save(lf, "getelementptr inbounds ", stacktype, "* ", stackp, ", i32 0, i32 ", baseIndex);
      load(lf, "load ", typeToLLVM(type), "* ", varp);
    }
    void emitLocation(LLVMFile lf) {
      if (!stacktype) fail;
      auto stackp = bitcastptr(lf, "i8", stacktype, "%__stackframe");
      load(lf, "getelementptr inbounds ", stacktype, "* ", stackp, ", i32 0, i32 ", baseIndex);
    }
    IType valueType() {
      return type;
    }
  }
  IType type;
  string name;
  int baseIndex;
  string stacktype;
  this() { }
  this(IType t, int i, string s) {
    type = t;
    name = s;
    baseIndex = i;
    stacktype = frametypePlus(type);
  }
  override string getIdentifier() { return name; }
  // Variable has no modifiable sub-expressions,
  // and we WANT modifications to refer back to the original!
  // (for instance, base_offset rewrites)
  // TODO: find some way to make this safe(r)
  override Variable dup() { return this; }
  mixin defaultIterate!();
  string toString() {
    if (name) return name;
    return Format("[ var of "[], type, " at "[], baseIndex, "]"[]);
  }
  void registerDwarf2(Dwarf2Controller dwarf2) {
    if (name && !name.startsWith("__temp"[])) {
      /*auto ty = resolveType(type);
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
        data ~= ".byte\t2f-1f\t/* fbreg, offset * /";
        data ~= "1:";
        data ~= qformat(".byte\t"[], hex(DW.OP_fbreg), "\t/* fbreg * /"[]);
        data ~= qformat(".sleb128\t"[], baseOffset, "\t/* base offset * /"[]);
        data ~= "2:";
      }
      dwarf2.add(varinfo);
      */
      todo("Variable::registerDwarf2");
    }
  }
}

class StackOffsetLocation : Expr {
  int offs;
  IType type;
  this(int o, IType t) { offs = o; type = t; }
  mixin defaultIterate!();
  override {
    StackOffsetLocation dup() { return fastalloc!(StackOffsetLocation)(offs, type); }
    IType valueType() { return type; }
    void emitLLVM(LLVMFile lf) {
      todo("StackOffsetLocation::emitLLVM");
      /*if (isARM) {
        lookupOp("+", new Register!("ebp"), mkInt(offs)).emitLLVM(lf);
      } else {
        lf.loadAddress(qformat(offs, "(%ebp)"), "%eax");
        lf.pushStack("%eax", nativePtrSize);
      }*/     
    }
    string toString() { return qformat(type, ": stack[", offs, "]"); }
  }
}
