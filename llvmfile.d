module llvmfile;

import std.string: find, atoi, strip;
import tools.base: slice, endsWith;

string datalayout;
string xbreak;
string preserve;

class LLVMFile {
  bool optimize, debugmode, profilemode;
  string fn;
  string[] sectionNameStack;
  string[string] sectionStore;
  string curSection, curSectionName;
  
  bool[string] doOnce;
  
  this(bool optimize, bool debugmode, bool profilemode, string filename) {
    this.optimize = optimize;
    this.debugmode = debugmode;
    this.profilemode = profilemode;
    this.fn = filename;
  }
  void beginSection(string name) {
    if (curSectionName) {
      sectionNameStack ~= curSectionName;
      sectionStore[curSectionName] = curSection;
    }
    curSectionName = name;
    curSection = null;
  }
  string endSection(string s) {
    if (curSectionName != s) fail;
    auto res = curSection;
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
  void put(string s) { // TODO builder of some kind
    curSection ~= s;
  }
  void putSection(string sec, string s) { // TODO builder some more
    // logln(fn, "(", curSectionName, "): put into ", sec, ": ", s);
    if (!curSectionName) fail;
    if (curSectionName == sec) {
      put(s);
      return;
    }
    sectionStore[sec] ~= s;
  }
  void dumpLLVM(void delegate(string) write) {
    if (!curSection) fail;
    write(curSection);
  }
  
  string[] exprs;
  int count;
  
  string[string] decls;
  bool[string] undecls;
  
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
    .put(this, "br label %", l);
    .put(this, l, ":");
  }
  int getId() { return count++; }
  string getVar() { return qformat("%var", getId()); }
  string save(string s) {
    auto id = getVar();
    .put(this, id, " = ", s);
    if (xbreak) {
      auto b = xbreak, a = b.slice("_");
      if (fn.find(a) != -1 && id == b)
        fail;
    }
    // if (id == "%var334" && fn.find("socket") != -1) fail;
    return id;
  }
  void load(string s) {
    push(save(s));
  }
  string allocLabel(string base = null) {
    if (!base) base = "label_";
    return qformat(base, count++);
  }
  string allocData(string base, ubyte[] data) {
    auto name = qformat(base, count++);
    string dataf;
    foreach (value; data) {
      if (dataf) dataf ~= ", ";
      dataf ~= qformat("i8 ", value);
    }
    .putSection(this, "module", "@", name, " = private constant [", data.length, " x i8] [", dataf, "], align 1");
    // .putSection(this, "module", "@", name, ".full = private constant [", data.length, " x i8] [", dataf, "], align 1");
    // .putSection(this, "module", "@", name, " = global i8* bitcast([", data.length, " x i8]* @", name, ".full to i8*)");
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

void put(T...)(LLVMFile lf, T t) {
  static if (is(T: string)) lf.put(t);
  else lf.put(qformat(t));
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

string allocConstant(LLVMFile lf, string name, ubyte[] data, bool priv) {
  lf.undecls[name] = true;
  if (once(lf, "constant ", name))
    putSection(lf, "module", "@", name, " = "~(priv?"private ":" ")~"constant ", toLLVMArray(1, data), ", align 16");
  return name;
}

string allocLongstant(LLVMFile lf, string name, string[] data, bool priv) {
  lf.undecls[name] = true;
  if (once(lf, "longstant ", name))
    putSection(lf, "module", "@", name, " = "~(priv?"private ":" ")~"constant ", toLLVMArray(4, data), ", align 16");
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
  if (type.endsWith(">")) mode = ", align 16";
  putSection(lf, "function_allocas", ap, " = alloca ", type, ", i32 ", size, mode);
  // auto ap = save(lf, "alloca i8, i32 ", size);
  return ap;
}

void checkcasttypes(string from, string to) {
  if (from.endsWith("}*") && to.endsWith(">*")) {
    logln("Cannot safely cast struct pointers to vector pointers as they have differing alignment");
    logln("  from: ", from);
    logln("    to: ", to);
    // fail;
  }
}

string bitcastptr(LLVMFile lf, string from, string to, string v) {
  if (from.endsWith("}") && to.endsWith(">"))
    checkcasttypes(from~"*", to~"*");
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

extern(C) string readback(string);
string[string] excache;
string readllex(string expr) {
  if (auto p = expr in excache) return *p;
  {
    auto num = expr.atoi();
    if (qformat(num) == expr) {
      excache[expr] = expr;
      return expr;
    }
  }
  auto code = "target datalayout = \""~datalayout~"\" define i32 @foo() { ret i32 "~expr~" }";
  auto res = readback("echo '"~code~"' |opt -std-compile-opts -S |grep 'ret i32' |sed -e 's/.*i32//'");
  if (qformat(res.atoi()) != res.strip()) {
    logln("from ", code);
    logln("to ", res);
    fail;
  }
  res = res.strip();
  // logln("record ", res, " ", expr);
  excache[expr] = res;
  return res;
}
