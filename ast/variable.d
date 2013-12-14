module ast.variable;

import ast.base, ast.opers, ast.literals, parseBase, ast.casting, ast.static_arrays, ast.namespace;

static int varcount;

import dwarf2, tools.log;
class Variable : LValue, Named {
  override {
    void emitLLVM(LLVMFile lf) {
      if (!stacktype) fail;
      auto stackp = bitcastptr(lf, "i8", stacktype, "%__stackframe");
      load(lf, "getelementptr inbounds ", stacktype, "* ", stackp, ", i32 0, i32 ", baseIndex);
      // logln(lf.count, ":", lf.fid, ": ", stacktype, " and ", type, " -- ", typeToLLVM(type), ", ", typeToLLVM(type, true));
      load(lf, "load ", typeToLLVM(type), "* ", lf.pop());
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
  int count;
  this() { }
  this(IType t, int i, string s) {
    type = t;
    name = s;
    baseIndex = i;
    count = varcount ++;
    // if (count == 15783) asm { int 3; }
    stacktype = frametypePlus(type);
    // logln(":", name, ": ", stacktype, " for ", type, " @", baseIndex);
  }
  override string getIdentifier() { return name; }
  // Variable has no modifiable sub-expressions,
  // and we WANT modifications to refer back to the original!
  // (for instance, base_offset rewrites)
  // TODO: find some way to make this safe(r)
  override Variable dup() { return this; }
  mixin defaultIterate!();
  Expr collapse() { return this; } // don't check, no foldopts
  string toString() {
    if (name) return name;
    return Format("[ var ", count, " of "[], type, " at "[], baseIndex, "]"[]);
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
