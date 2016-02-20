module llvmfile;

import std.string: find, atoi, strip, replace;
import tools.base: slice, endsWith, Stuple, stuple, between, sw = startsWith;

string datalayout;
string xbreak;
string preserve;

Object freelist_sync;
static this() { freelist_sync = new Object; }

void own_append(T, U)(ref T array, U value) {
  auto backup = array;
  array ~= value;
  if (backup.ptr !is array.ptr) delete backup;
}

string[][][int] freelist;
Stuple!(string[], int) allocTup(int i) {
  synchronized(freelist_sync) {
    if (auto p = i in freelist) {
      auto res = (*p)[0];
      (*p) = (*p)[1..$];
      if (!(*p).length) freelist.remove(i);
      // logln("allocNewList cached(", i, ")");
      return stuple(res, 0);
    }
  }
  // logln("allocNewList(", i, ")");
  return stuple(new string[i], 0);
}
void listfree(string[] arr) {
  auto len = arr.length;
  // logln("listfree(", len, ")");
  synchronized(freelist_sync) {
    if (auto p = len in freelist) (*p) ~= arr;
    else {
      freelist[len] = null;
      freelist[len] ~= arr;
    }
  }
}

template ForwardToList(string name, alias P, alias M, R, T...) {
  mixin(`R `~name~`(T t) {
    if (P) (*P).`~name~`(t);
    M.`~name~`(t);
  }`);
}

struct AppenderList {
  TextAppender me;
  AppenderList* prev;
  string toString() { if (prev) return qformat(*prev, " -> ", me); return qformat(me); }
  mixin ForwardToList!("free",     prev, me, void);
  mixin ForwardToList!("flush",    prev, me, void, void delegate(string));
  void setBottom(AppenderList* to) {
    auto cur = this;
    while (cur.prev) cur = cur.prev;
    cur.prev = to;
  }
  void opCatAssign(string s) {
    me ~= s;
  }
}

template ForwardToPtr(string name, alias P, R, T...) {
  mixin(`R `~name~`(T t) {
    if (P) (*P).`~name~`(t);
  }`);
}

struct SuperAppender {
  AppenderList* ptr;
  mixin ForwardToPtr!("free",     ptr, void);
  mixin ForwardToPtr!("flush",    ptr, void, void delegate(string));
  string toString() { if (!ptr) return "{}"; return qformat("{", *ptr, "}"); }
  void opAssign(void* p) {
    if (p) fail;
    ptr = null;
  }
  void setBottom(AppenderList* ap) {
    if (!ptr) ptr = ap;
    else ptr.setBottom(ap);
  }
  void opCatAssign(string s) {
    if (!ptr) ptr = new AppenderList;
    (*ptr) ~= s;
  }
  void opCatAssign(SuperAppender sa) {
    if (ptr && ptr is sa.ptr) asm { int 3; }
    sa.setBottom(ptr);
    ptr = sa.ptr;
  }
}

struct TextAppender {
  Stuple!(string[], int)[] superlist;
  int i = 16;
  string toString() { return qformat(superlist); }
  void allocNewList() {
    superlist ~= allocTup(i);
    i *= 2;
  }
  void opCatAssign(string s) {
    if (!superlist) allocNewList;
    auto sl = &superlist[$-1];
    if (sl._1 == sl._0.length) {
      allocNewList;
      sl = &superlist[$-1];
    }
    sl._0[sl._1++] = s;
  }
  void clear() {
    superlist = null;
  }
  void free() {
    foreach (tup; superlist) listfree(tup._0);
    delete superlist;
    clear;
  }
  void opAssign(void* p) { // = null
    if (p) fail;
    clear;
  }
  void flush(void delegate(string) dg) {
    foreach (array; superlist) foreach (fragment; array._0[0..array._1])
      dg(fragment);
    free;
  }
}

class LLVMFile {
  bool optimize;
  bool debugmode, debugmode_dwarf;
  bool profilemode, profile_branches;
  bool addrspace0;
  int[int] branchValues;
  
  string currentFunctionDwarfMetadata;
  string[] dwarf_subprogs; // add one for every function we emit
  string fn, fid;
  string[] sectionNameStack;
  SuperAppender[string] sectionStore;
  SuperAppender curSection;
  TextAppender metadata;
  int metadata_count;
  string curSectionName;
  string curSectionAnnotation;
  
  bool[string] doOnce;
  
  this(bool optimize, bool debugmode, bool debugmode_dwarf, bool profilemode, string filename) {
    this.optimize = optimize;
    this.debugmode = debugmode;
    this.debugmode_dwarf = debugmode_dwarf;
    this.profilemode = profilemode;
    this.fn = filename;
    this.fid = fn.endsWith(".nt").replace("/", "_");
    assert(!!fid);
  }
  void beginSection(string name) {
    if (curSectionName) {
      sectionNameStack ~= curSectionName;
      sectionStore[curSectionName] = curSection;
    }
    curSectionName = name;
    curSection = null;
    curSectionAnnotation = null;
  }
  void free() {
    if (sectionStore.keys.length) {
      logln("Leftover sections: ", sectionStore.keys);
    }
    curSection.free;
  }
  SuperAppender endSection(string s) {
    if (curSectionName != s) fail;
    auto res = curSection;
    curSectionAnnotation = null;
    if (!sectionNameStack) {
      curSectionName = null;
      curSection = null;
      return res;
    }
    curSectionName = sectionNameStack[$-1];
    sectionNameStack = sectionNameStack[0..$-1];
    curSection = sectionStore[curSectionName];
    sectionStore.remove(curSectionName);
    return res;
  }
  string addMetadata(string data) {
    auto id = metadata_count++;
    metadata ~= qformat("!", id, " = metadata !{", data, "}\n");
    return qformat("!", id);
  }
  void put(SuperAppender app) {
    curSection ~= app;
  }
  void put(string s) {
    curSection ~= s;
  }
  void putSection(string sec, string s) { // TODO builder some more
    // logln(fn, "(", curSectionName, "): put into ", sec, ": ", s);
    if (!curSectionName) fail;
    if (curSectionName == sec) {
      put(s);
      return;
    }
    if (!(sec in sectionStore))
      sectionStore[sec] = SuperAppender();
    sectionStore[sec] ~= s;
  }
  void dumpLLVM(void delegate(string) write) {
    if (!curSectionName) fail;
    curSection.flush(write);
    metadata.flush(write); // at the end
  }
  
  string[] exprs;
  int count;
  
  string[string] decls;
  bool[string] undecls;
  string[string] varcache;
  
  void push(string s) {
    if (!s.length) fail;
    exprs ~= s;
  }
  string pop() {
    if (!exprs.length) fail;
    auto res = exprs[$-1];
    exprs = exprs[0..$-1];
    return res;
  }
  bool[string] targeted;
  void emitLabel(string l, bool forwardsOnly = false) {
    if (forwardsOnly && !(l in targeted)) return; // not used
    varcache = null; // basic block end, discard cache
    .put(this, "br label %", l);
    put(l); put(":\n");
  }
  int getId() { return count++; }
  string getVar() { return qformat("%var", getId()); }
  void bbclear() { varcache = null; }
  static bool sideeffecty(string s) {
    if (s.sw("call")) return true;
    if (s.sw("load")) return true;
    if (s.sw("alloca")) return true;
    return false;
  }
  string save(string s) {
    if (auto p = s in varcache) {
      // logln(s, " cached to ", *p);
      return *p;
    }
    auto id = getVar();
    if (!sideeffecty(s)) {
      // logln("insert cache: ", s, " = ", id);
      varcache[s] = id;
    }
    
    .put(this, id, " = ", s);
    if (xbreak) {
      auto b = xbreak, a = b.slice("_");
      if (fn.find(a) != -1 && id == b)
        fail;
    }
    return id;
  }
  void load(string s) {
    push(save(s));
  }
  string allocLabel(string base = null) {
    if (!base) base = "label_";
    return qformat(base, count++);
  }
  string allocData(string base, ubyte[] data, bool addnum = true) {
    auto name = base;
    if (addnum) name = qformat(name, "_", fid, count++);
    
    if (once(name)) {
      string dataf;
      foreach (value; data) {
        if (dataf) dataf ~= ", ";
        dataf ~= qformat("i8 ", value);
      }
      // decls[name] = qformat("@", name, " = private constant [", data.length, " x i8] [", dataf, "], align 1");
      .putSection(this, "module", "@", name, " = private constant [", data.length, " x i8] [", dataf, "], align 1");
      // .putSection(this, "module", "@", name, ".full = private constant [", data.length, " x i8] [", dataf, "], align 1");
      // .putSection(this, "module", "@", name, " = global i8* bitcast([", data.length, " x i8]* @", name, ".full to i8*)");
    }
    return name;
  }
  bool once(string s) {
    if (s in doOnce) return false;
    doOnce[s] = true;
    return true;
  }
}

bool once(T...)(LLVMFile lf, T t) {
  return lf.once(qformat(t));
}

import quickformat;

void setFunctionAnnotation(LLVMFile lf, string s) {
  lf.curSectionAnnotation = s;
}

void put(T...)(LLVMFile lf, T t) {
  static if (is(T: string)) lf.put(t);
  else lf.put(qformat(t));
  if (lf.curSectionAnnotation) lf.put(lf.curSectionAnnotation);
  lf.put("\n");
}

void push(T...)(LLVMFile lf, T t) {
  lf.push(qformat(t));
}

void putSection(T...)(LLVMFile lf, string section, T t) {
  static if (is(T: string)) lf.putSection(section, t);
  else lf.putSection(section, qformat(t));
  lf.putSection(section, "\n");
}

string addMetadata(T...)(LLVMFile lf, T t) {
  return lf.addMetadata(qformat(t));
}

// template so we can use Expr without importing base
string save(T...)(LLVMFile lf, T t) {
  static if (T.length == 1 && is(typeof(t[0].emitLLVM))) {
    auto ex = t[0];
    auto pre = lf.exprs.length;
    ex.emitLLVM(lf);
    if (lf.exprs.length - pre != 1) {
      logln("Expected ", pre+1, ", got ", lf.exprs.length, " after emit of ", ex);
      asm { int 3; }
      ex.emitLLVM(lf);
      fail;
    }
    return lf.pop();
  } else {
    return lf.save(qformat(t));
  }
}

void load(T...)(LLVMFile lf, T t) {
  lf.load(qformat(t));
}

void jump(LLVMFile lf, string dest) {
  lf.targeted[dest] = true;
  put(lf, "br label %", dest);
}

void jumpOn(LLVMFile lf, string dest) {
  lf.targeted[dest] = true;
  auto test = lf.pop();
  auto next = lf.allocLabel("cjump_else");
  put(lf, "br i1 ", test, ", label %", dest, ", label %", next);
  lf.emitLabel(next);
}

string toLLVMArray(T)(int size, T[] arr) {
  string type;
  if (size == -1)type = "i8*";
  if (size == 1) type = "i8";
  if (size == 2) type = "i16";
  if (size == 4) type = "i32";
  if (!type) fail;
  string res;
  foreach (val; arr) {
    if (res) res ~= ", ";
    res ~= qformat(type, " ", val);
  }
  return qformat("[", arr.length, " x ", type, "] [", res, "]");
}

string allocConstant(LLVMFile lf, string name, ubyte[] data, bool priv, bool weak = false) {
  lf.undecls[name] = true;
  if (once(lf, "constant ", name)) {
    if (weak) {
      putSection(lf, "module", "@", name, " = weak_odr global ", toLLVMArray(1, data), ", align 16");
    } else {
      putSection(lf, "module", "@", name, " = "~(priv?"private ":"")~"unnamed_addr constant ", toLLVMArray(1, data), ", align 16");
    }
  }
  return name;
}

string allocLongstant(LLVMFile lf, string name, string[] data, bool priv, bool weak = false) {
  lf.undecls[name] = true;
  if (once(lf, "longstant ", name)) {
    if (weak) { 
      putSection(lf, "module", "@", name, " = weak_odr global ", toLLVMArray(4, data), ", align 16");
    } else {
      putSection(lf, "module", "@", name, " = "~(priv?"private ":"")~"unnamed_addr constant ", toLLVMArray(4, data), ", align 16");
    }
  }
  return name;
}

void formTuple(LLVMFile lf, string[] args...) {
  // logln("formTuple ", args);
  if (args.length % 2) fail;
  string tuptype;
  foreach (i, t; args) if (i%2 == 0) {
    if (tuptype) tuptype ~= ", ";
    tuptype ~= t;
  }
  tuptype = qformat("{", tuptype, "}");
  string res = "undef";
  foreach (i, type; args) if (i%2 == 0) {
    auto arg = args[i+1];
    if (type.find("{") != -1) {
      // logln("formTuple(", args, ")");
      // fail;
    }
    res = save(lf, "insertvalue ", tuptype, " ", res, ", ", type, " ", arg, ", ", i/2);
  }
  lf.push(res);
}

string alloca(LLVMFile lf, string size, string type = null) {
  auto ap = lf.getVar();
  if (!type) type = "i8";
  string mode;
  if (llvmTypeIs16Aligned(type)) mode = ", align 16";
  putSection(lf, "function_allocas", ap, " = alloca ", type, ", i32 ", size, mode);
  // auto ap = save(lf, "alloca i8, i32 ", size);
  return ap;
}

void checkcastptrtypes(string from, string to) {
  if (llvmTypeIs16Aligned(from) != llvmTypeIs16Aligned(to)) {
    logln("Cannot safely cast struct pointers to vector pointers as they have differing alignment");
    logln("  from: ", from);
    logln("    to: ", to);
    // fail;
  }
}

void checkcasttypes(string from, string to) {
  checkcastptrtypes(from~"*", to~"*");
}

string bitcastptr(LLVMFile lf, string from, string to, string v) {
  if (from.endsWith("}") && to.endsWith(">"))
    checkcastptrtypes(from, to);
  return save(lf, "bitcast ", from, "* ", v, " to ", to, "*");
}

extern(C) void llcast(LLVMFile lf, string from, string to, string v, string fromsize = null);

import tools.log, tools.base: fail, toStringz, Format;
extern(C) int getpid();
import std.process: _system = system;
void todo(string msg = null) {
  auto pid = getpid();
  _system(Format("gdb --batch -n -ex thread -ex bt -p ", pid));
  logln("TODO ", msg);
  fail;
}

import cache;

int i;
extern(C) string readback(string);
extern(C) string canonify(string);
string[string] excache;
string readllex(string expr) {
  auto key = canonify(expr);
  if (auto p = key in excache) return *p;
  {
    auto num = expr.atoi();
    if (qformat(num) == expr) {
      excache[key] = expr;
      return expr;
    }
  }
  
  auto cachekey = expr;
  if (cachekey.find("\n") != -1) {
    logln("!? ", cachekey);
    fail;
  }
  // TODO include datalayout in key if we ever support x86_64
  if (auto cache = read_cache(cachekey, null))
    return cache;
  
  auto code = "target datalayout = \""~datalayout~"\" define i32 @foo() { ret i32 "~key~" }";
  auto c2 = code.replace("\\", "\\\\");
  auto c3 = c2.replace("\"", "\\\"");
  auto c4 = "sh -c \"echo '"
    ~c3
    ~"' |opt -O3 -S |grep 'ret i32' |sed -e 's/.*i32//'\"";
  scope(exit) {
    delete c4;
    if (c3 !is c2) delete c3;
    if (c2 !is code) delete c2;
    delete code;
  }
  auto res = readback(c4);
  if (qformat(res.atoi()) != res.strip()) {
    if (!res.strip().length) {
      logln("opt not found or produced no output. Do you have LLVM installed?");
      fail;
    }
    logln("from ", code);
    logln("to ", res);
    fail;
  }
  res = res.strip();
  // logln(i++, ": record ", res, " ", key);
  excache[key] = res;
  write_cache(cachekey, null, res);
  return res;
}

string llexcachecheck(string key) {
  if (auto p = key in excache) return *p;
  return key;
}

int llvmver_cache = -1;
int llvmver() {
  if (llvmver_cache != -1) return llvmver_cache;
  auto res = readback("opt --version").between("LLVM version ", "\n");
  if (!res.length) throw new Exception("LLVM must be installed and its command line tools must be in the path!");
  assert(res.length >= 3 && res[1] == '.' &&
    res[0] >= '0' && res[0] <= '9' &&
    res[2] >= '0' && res[2] <= '9');
  int ires = (res[0] - '0') * 10 + (res[2] - '0');
  llvmver_cache = ires;
  return ires;
}

alias void delegate(string) structDecompose_dg;
extern(C) void structDecompose(string str, structDecompose_dg);
bool llvmTypeIs16Aligned(string s) {
  // TODO parse for vec3/vec4
  if (s.endsWith(">")) return true;
  // pointer targets may require 16-alignment
  // however, the pointer itself doesn't
  if (s.endsWith("*")) return false; 
  if (s.endsWith("}")) {
    bool res;
    structDecompose(s, (string s) { if (llvmTypeIs16Aligned(s)) res = true; });
    return res;
  }
  // logln(s);
  // fail;
  return false;
}

string getelementptr_ex(string basetype, string value, string indexes) {
  if (llvmver() >= 37) {
    return qformat("getelementptr(", basetype, ", ", basetype, "* ", value, ", ", indexes, ")");
  }
  return qformat("getelementptr(", basetype, "* ", value, ", ", indexes, ")");
}

string getelementptr_inbounds(string basetype, string value, string indexes) {
  if (llvmver() >= 37) {
    return qformat("getelementptr inbounds ", basetype, ", ", basetype, "* ", value, ", ", indexes);
  }
  return qformat("getelementptr inbounds ", basetype, "* ", value, ", ", indexes);
}

string ll_load(string basetype, string value) {
  if (llvmver() >= 37) {
    return qformat("load ", basetype, ", ", basetype, "* ", value);
  }
  return qformat("load ", basetype, "* ", value);
}

string ll_load(string basetype, string ptrtype, string value) {
  if (llvmver() >= 37) {
    return qformat("load ", basetype, ", ", ptrtype, " ", value);
  }
  return qformat("load ", ptrtype, " ", value);
}

void splitstore(LLVMFile lf, string fromtype, string from, string totype, string to, bool addrspace1, bool nontemporal = false) {
  bool fromIsStruct = !!fromtype.endsWith("}"), toIsStruct = !!totype.endsWith("}");
  if (fromIsStruct != toIsStruct) fail(qformat("incompatible types: ", fromtype, " into ", totype));
  bool isStruct = fromIsStruct;
  string nontemp;
  if (nontemporal) {
    nontemp = qformat(", !nontemporal ", addMetadata(lf, "i32 1"));
  }
  if (!isStruct) {
    if (addrspace1) {
      string addrspacecast = "bitcast ";
      if (llvmver() >= 34) addrspacecast = "addrspacecast ";
      to = save(lf, addrspacecast, totype, "* ", to, " to ", totype, " addrspace(1)*");
      put(lf, "store ", fromtype, " ", from, ", ", totype, " addrspace(1)* ", to, nontemp);
    } else {
      put(lf, "store ", fromtype, " ", from, ", ", totype, "* ", to, nontemp);
    }
    return;
  }
  // to is actually pointer to totype struct, but don't mind
  int i;
  string[] types2;
  structDecompose(totype, (string s) { types2 ~= s; });
  structDecompose(fromtype, (string subtype) {
    auto elem = save(lf, "extractvalue ", fromtype, " ", from, ", ", i);
    string gep;
    if (llvmver() < 37) {
      gep = save(lf, "getelementptr inbounds ", totype, "* ", to, ", i32 0, i32 ", i);
    } else {
      gep = save(lf, "getelementptr inbounds ", totype, ", ", totype, "* ", to, ", i32 0, i32 ", i);
    }
    splitstore(lf, subtype, elem, types2[i], gep, addrspace1, nontemporal);
    i++;
  });
}
