module casts;

import tools.log, tools.ctfe, tools.compat: min;
import tools.base: Format;

// list of class names to optimize
const string[] quicklist = [
  "ast.structure.Structure",
  "ast.structure.MemberAccess_LValue",
  "ast.types.Float",
  "ast.pointer.Pointer",
  "ast.types.SysInt", 
  "ast.pointer.RefExpr",
  "ast.math.AsmIntBinopExpr",
  "ast.arrays.ArrayMaker",
  "ast.structure.StructLiteral",
  "ast.int_literal.IntExpr",
  "ast.propcall.MyPlaceholderExpr",
  "ast.casting.ReinterpretCast!(Expr).ReinterpretCast",
  "ast.propcall.FirstParamOverrideSpace",
  "ast.pointer.DerefExpr",
  "ast.casting.ReinterpretCast!(LValue).ReinterpretCast",
  "ast.variable.Variable",
  "ast.arrays.ExtArray",
  "ast.math.IntLiteralAsShort",
  "ast.fun.FunCall",
  "ast.modules.Module",
  "ast.types.Byte",
  "ast.literals.FloatExpr",
  "ast.casting.ReinterpretCast!(MValue).ReinterpretCast",
  "ast.fun.Function",
  "ast.globvars.GlobVar",
  "ast.arrays.Array",
  "ast.tuples.Tuple",
  "ast.types.Char",
  "ast.math.IntAsFloat",
  "ast.casting.ShortToIntCast",
  "ast.tuples.RefTuple",
  "ast.structure.RelMember",
  "ast.math.IntAsLong",
  "ast.scopes.Scope",
  "ast.types.Long",
  "ast.types.Short",
  "ast.math.FloatAsDouble",
  "ast.types.Double",
  "ast.vector.Vector",
  "ast.structure.MemberAccess_Expr",
  "ast.funcall.DgCall",
  "ast.literals.CValueAsPointer",
  "ast.aliasing.ExprAlias",
  "ast.literal_string.StringExpr",
  "ast.tuples.LValueAsMValue",
  "ast.static_arrays.DataExpr",
  "ast.vector.VecOp",
  "ast.static_arrays.StaticArray",
  "ast.aliasing.TypeAlias"
];

struct RadixTreeNode {
  string prefix;
  RadixTreeNode*[] children;
  int myID;
  string toString() {
    RadixTreeNode[] mew;
    foreach (entry; children) mew ~= *entry;
    string res = "[";
    if (prefix) res ~= "'"~prefix~"'";
    if (myID != -1) res ~= Format(" ", myID);
    if (mew.length) res ~= Format(" ", mew);
    res ~= "]";
    return res;
  }
  static {
    RadixTreeNode* alloc(string p, RadixTreeNode*[] ch, int i) {
      auto res = new RadixTreeNode;
      res.prefix = p;
      res.children = ch;
      res.myID = i;
      return res;
    }
  }
}

import quicksort;
RadixTreeNode* radixRoot;
void buildRadixTree() {
  auto ql = quicklist.dup;
  ql.qsort((string a, string b) {
    auto ml = min(a.length, b.length);
    for (int i = 0; i < ml; ++i) {
      if (a[i] < b[i]) return true;
      if (a[i] > b[i]) return false;
    }
    if (a.length) return false;
    else return true;
  });
  int count;
  RadixTreeNode* naive(string pref, string[] list) {
    assert(list.length);
    
    int from;
    RadixTreeNode*[] temp;
    char curPrefix;
    int myID = -1;
    int myIDPos = -1;
    void flush(int to) {
      if (from == to) return;
      string[] sgm;
      foreach (i, entry; list[from .. to]) {
        if (from + i == myIDPos) continue;
        sgm ~= entry[1 .. $];
      }
      if (sgm.length)
        temp ~= naive(""~curPrefix, sgm);
      from = to;
    }
    foreach (id, entry; list) {
      if (!entry.length) {
        assert(myID == -1);
        myID = count++;
        myIDPos = id;
      } else if (id == from) {
        curPrefix = entry[0];
      } else if (entry[0] != curPrefix) {
        flush(id);
        curPrefix = entry[0];
      } // else continue
    }
    flush(list.length);
    return RadixTreeNode.alloc(pref, temp, myID);
  }
  void opt(RadixTreeNode* node) {
    while (node.children.length == 1 && node.myID == -1) {
      node.prefix ~= node.children[0].prefix;
      node.myID = node.children[0].myID;
      node.children = node.children[0].children;
    }
    foreach (child; node.children) {
      opt(child);
    }
  }
  radixRoot = naive("", ql);
  opt(radixRoot);
  // logln("root node ", *radixRoot);
  // asm { int 3; }
}

import parseBase: startsWith;
int getId(string s) {
  auto cur = radixRoot;
  if (!s.startsWith(cur.prefix)) return -1;
  s = s[cur.prefix.length .. $];
  restart:
  foreach (child; cur.children) {
    auto cp = child.prefix;
    if (s.length >= cp.length && s[0 .. cp.length] == cp) {
      if (s.length == cp.length) return child.myID;
      s = s[cp.length .. $];
      cur = child;
      goto restart;
    }
  }
  return -1;
}

static this() { buildRadixTree(); }

struct _fastcast(T) {
  const ptrdiff_t INVALID = 0xffff; // magic numbah
  static ptrdiff_t[quicklist.length] offsets;
  T opCall(U)(U u) {
    if (!u) return null;
    // logln("Cast ", (cast(Object) u).classinfo.name);
    Object obj;
    static if (!is(U: Object)) { // interface
      auto ptr = **cast(Interface***) u;
      obj = cast(Object) (cast(void*) u - ptr.offset);
    } else {
      obj = u;
    }
    auto id = getId(obj.classinfo.name);
    if (id == -1) return cast(T) u;
    auto hint = offsets[id];
    if (hint == INVALID) return null;
    if (!hint) {
      auto res = cast(T) obj;
      if (res) 
        offsets[id] = (cast(void*) res - cast(void*) obj) + 1;
      else
        offsets[id] = INVALID;
      return res;
    }
    return cast(T) (cast(void*) obj + (hint - 1));
  }
  alias opCall opCat;
}

template fastcast(T) {
  _fastcast!(T) fastcast;
}
