module parseBase;

import casts;

string mystripl(string s) {
  while (s.length && (
    s[0] == ' '  || s[0] == '\t' ||
    s[0] == '\n' || s[0] == '\r'
  )) {
    s = s[1 .. $];
  }
  return s;
}

int[int] accesses;

import tools.base, errors;
struct StatCache {
  tools.base.Stuple!(Object, char*, int)[char*] cache;
  int depth;
  tools.base.Stuple!(Object, char*)* opIn_r(char* p) {
    auto res = p in cache;
    if (!res) return null;
    auto delta = depth - res._2;
    if (!(delta in accesses)) accesses[delta] = 0;
    accesses[delta] ++;
    return cast(tools.base.Stuple!(Object, char*)*) res;
  }
  void opIndexAssign(tools.base.Stuple!(Object, char*) thing, char* idx) {
    cache[idx] = stuple(thing._0, thing._1, depth++);
  }
}

struct SpeedCache {
  tools.base.Stuple!(char*, Object, char*)[24] cache;
  int curPos;
  tools.base.Stuple!(Object, char*)* opIn_r(char* p) {
    int i = curPos - 1;
    if (i == -1) i = cache.length - 1;
    while (i != curPos) {
      if (cache[i]._0 == p)
        return cast(tools.base.Stuple!(Object, char*)*) &cache[i]._1;
      if (--i < 0) i += cache.length;
    }
    return null;
  }
  void opIndexAssign(tools.base.Stuple!(Object, char*) thing, char* idx) {
    cache[curPos++] = stuple(idx, thing._0, thing._1);
    if (curPos == cache.length) curPos = 0;
  }
}

enum Scheme { Binary, Octal, Decimal, Hex }
bool gotInt(ref string text, out int i) {
  auto t2 = text.mystripl();
  t2.eatComments();
  if (auto rest = t2.startsWith("-")) {
    return gotInt(rest, i)
      && (
        i = -i,
        (text = rest),
        true
      );
  }
  ubyte ub;
  bool accept(ubyte from, ubyte to = 0xff) {
    if (!t2.length) return false;
    ubyte nub = t2[0];
    if (nub < from) return false;
    if (to != 0xff) { if (nub > to) return false; }
    else { if (nub > from) return false; }
    nub -= from;
    t2.take();
    ub = nub;
    return true;
  }
  
  int res;
  bool getDigits(Scheme scheme) {
    static int[4] factor = [2, 8, 10, 16];
    bool gotSomeDigits = false;
    outer:while (true) {
      while (accept('_')) { }
      switch (scheme) {
        case Scheme.Hex:
          if (accept('a', 'f')) { ub += 10; break; }
          if (accept('A', 'F')) { ub += 10; break; }
        case Scheme.Decimal: if (accept('0', '9')) break;
        case Scheme.Octal:   if (accept('0', '7')) break;
        case Scheme.Binary:  if (accept('0', '1')) break;
        default: break outer;
      }
      gotSomeDigits = true;
      assert(ub < factor[scheme]);
      res = res * factor[scheme] + ub;
    }
    return gotSomeDigits;
  }

  if (accept('0')) {
    if (accept('b') || accept('B')) {
      if (!getDigits(Scheme.Binary)) return false;
    } else if (accept('x') || accept('X')) {
      if (!getDigits(Scheme.Hex)) return false;
    } else {
      if (!getDigits(Scheme.Octal)) res = 0;
    }
  } else {
    if (!getDigits(Scheme.Decimal)) return false;
  }
  i = res;
  text = t2;
  return true;
}

import tools.compat: replace;
import tools.base: Stuple, stuple;

// TODO: unicode
bool isNormal(wchar c) {
  return c in Range['a'..'z'].endIncl ||
         c in Range['A'..'Z'].endIncl ||
         c in Range['0'..'9'].endIncl ||
         "_µ".find(c) != -1;
}

// TODO: NOT THREADSAFE
string lastAccepted, lastAccepted_stripped;
bool accept(ref string s, string t) {
  string s2;
  bool sep = t.length && t[$-1] == ' ';
  debug if (t !is t.strip()) {
    logln("bad t: '", t, "'");
    asm { int 3; }
  }
  if (s is lastAccepted) {
    s2 = lastAccepted_stripped;
  } else {
    s2 = s.mystripl();
    s2.eatComments();
    lastAccepted = s;
    lastAccepted_stripped = s2;
  }
  if (t == "<-" && s2.startsWith("←")) t = "←";
  
  size_t idx = t.length;
  return s2.startsWith(t) && (s2.length == t.length || t.length && !isNormal(t.toUTF16()[$-1]) || !isNormal(s2.decode(idx))) && (s = s2[t.length .. $], true) && (
    !sep || !s.length || s[0] == ' ' && (s = s[1 .. $], true)
  );
}

bool mustAccept(ref string s, string t, lazy string err) {
  if (s.accept(t)) return true;
  s.failparse(err());
}

bool bjoin(ref string s, lazy bool c1, lazy bool c2, void delegate() dg,
           bool allowEmpty = true) {
  auto s2 = s;
  if (!c1) { s = s2; return allowEmpty; }
  dg();
  while (true) {
    s2 = s;
    if (!c2) { s = s2; return true; }
    s2 = s;
    if (!c1) { s = s2; return false; }
    dg();
  }
}

// while expr
bool many(ref string s, lazy bool b, void delegate() dg = null, string abort = null) {
  while (true) {
    auto s2 = s, s3 = s2;
    if (abort && s3.accept(abort)
        ||
        !b()
    ) {
      s = s2;
      break;
    }
    if (dg) dg();
  }
  return true;
}

import std.utf;
bool gotIdentifier(ref string text, out string ident, bool acceptDots = false) {
  auto t2 = text.mystripl();
  t2.eatComments();
  bool isValid(wchar w, bool first = false) {
    return isNormal(w) || (!first && w == '-') || (acceptDots && w == '.');
  }
  // array length special handling
  if (t2.length && t2[0] == '$') { text = t2; ident = "$"; return true; }
  size_t idx = 0;
  if (!t2.length || !isValid(cast(wchar) t2.decode(idx), true)) return false;
  auto identlen = 0, backup = t2;
  do {
    t2.take();
    identlen ++;
  } while (t2.length && isValid(t2[0]));
  ident = backup[0 .. identlen];
  text = t2;
  return true;
}

bool[string] reserved;
static this() {
  reserved["auto"] = true;
  reserved["return"] = true;
}

bool gotValidIdentifier(ref string text, out string ident, bool acceptDots = false) {
  string t2 = text;
  if (t2.gotIdentifier(ident, acceptDots) && !(ident in reserved)) {
    text = t2;
    return true;
  }
  return false;
}

// This isn't a symbol! Maybe I was wrong about the dash .. 
// Remove the last dash part from "id" that was taken from "text"
// and re-add it to "text" via dark pointer magic.
bool eatDash(ref string text, ref string id) {
  auto dp = id.rfind("-");
  if (dp == -1) return false;
  auto removed = id.length - dp;
  id = id[0 .. dp];
  // give back
  text = (text.ptr - removed)[0 .. text.length + removed];
  return true;
}

// see above
bool eatDot(ref string text, ref string id) {
  auto dp = id.rfind(".");
  if (dp == -1) return false;
  auto removed = id.length - dp;
  id = id[0 .. dp];
  // give back also
  text = (text.ptr - removed)[0 .. text.length + removed];
  return true;
}

bool ckbranch(ref string s, bool delegate()[] dgs...) {
  auto s2 = s;
  foreach (dg; dgs) {
    if (dg()) return true;
    s = s2;
  }
  return false;
}

bool verboseParser = false, verboseXML = false;

string[bool delegate(string)] condInfo;

alias Tuple!(string, bool delegate(string), ubyte, bool)
  RuleData;

const RULEPTR_SIZE_HAX = (Stuple!(RuleData)).sizeof;
void[RULEPTR_SIZE_HAX][] slab;
int slab_freeptr = -1, slab_top;

struct RuleStruct(alias A) {
  Stuple!(RuleData) tuple;
  bool fun(Params!(typeof(&A))[1 .. $] rest) {
    return A(&tuple, rest);
  }
}

template allocRuleData(alias A) {
  bool delegate(Params!(typeof(&A))[1 .. $])
  allocRuleData(RuleData rd, out int id) {
    void* res;
    if (slab_freeptr != -1) {
      res = slab[slab_freeptr].ptr;
      id = slab_freeptr;
      slab_freeptr = *cast(int*) res;
    } else {
      if (!slab) slab = new void[RULEPTR_SIZE_HAX][65536];
      if (slab_top >= slab.length) slab.length = slab.length * 2;
      id = slab_top;
      res = slab[slab_top++].ptr;
    }
    auto strp = cast(RuleStruct!(A)*) res;
    strp.tuple = stuple(rd);
    return &strp.fun;
  }
}

Object ardlock;
static this() { New(ardlock); }

void freeRuleData(int offs) {
  synchronized(ardlock) {
    auto ptr = slab[offs].ptr;
    *cast(int*) ptr = slab_freeptr;
    slab_freeptr = offs;
  }
}

bool sectionStartsWith(string section, string rule) {
  if (section == rule) return true;
  auto match = section.startsWith(rule);
  // only count hits that match a complete section
  return match.length && match[0] == '.';
}

bool delegate(string) matchrule(string rules, out int id) {
  bool delegate(string) res;
  auto rules_backup = rules;
  while (rules.length) {
    auto rule = rules.slice(" ");
    bool smaller, greater, equal, before, after;
    assert(rule.length);
    auto first = rule[0], rest = rule[1 .. $];
    switch (first) {
      case '<': smaller = true; rule = rest; break;
      case '>': greater = true; rule = rest; break;
      case '=': equal = true; rule = rest; break;
      case '^': before = true; rule = rest; break;
      case '_': after = true; rule = rest; break;
      default: break;
    }
    
    if (!smaller && !greater && !equal && !before && !after)
      smaller = equal = true; // default
    // different modes
    assert((smaller || greater || equal) ^ before ^ after);
    
    // cases: smaller, greater, equal, before, after
    static bool fun(Stuple!(RuleData)* data, string text) {
      auto op1 = data._1;
      if (op1 && !op1(text)) return false;
      // avoid allocation from ~"."
      auto rule = data._0, cases = data._2;
      if ((cases&1) && text.sectionStartsWith(rule)) // all "below" in the tree
        return true;
      if ((cases&4) && text == rule)
        return true;
      if ((cases&2) && !text.sectionStartsWith(rule)) // arguable
        return true;
      
      auto hit = &data._3;
      if (cases&8) {
        if (text.sectionStartsWith(rule))
          *hit = true;
        return !*hit;
      }
      if (cases&16) {
        if (text.sectionStartsWith(rule))
          *hit = true;
        else return *hit;
      }
      return false;
    };
    alias allocRuleData!(fun) ard;
    synchronized(ardlock) {
      res = ard(
        rule, res,
        (smaller<<0) | (greater<<1) | (equal<<2) | (before<<3) | (after<<4),
        false, id
      );
    }
    // res = res /apply/ (bool delegate(string) dg, string s) { auto res = dg(s); logln(s, " -> ", res); return res; };
  }
  // condInfo[res] = rules_backup;
  return res;
}

struct ParseCtl {
  int state;
  string reason;
  const ParseCtl AcceptAbort = {0}, RejectAbort = {1}, AcceptCont = {2};
  static ParseCtl RejectCont(string reason) {
    ParseCtl res;
    res.state = 3;
    res.reason = reason;
    return res;
  }
  string decode() {
    switch (state) {
      case 0: return "AcceptAbort";
      case 1: return "RejectAbort";
      case 2: return "AcceptCont";
      case 3: return "RejectCont:"~reason;
    }
  }
}

import tools.functional;
struct ParseCb {
  Object delegate(ref string text,
    bool delegate(string),
    ParseCtl delegate(Object) accept
  ) dg;
  bool delegate(string) cur;
  Object opCall(T...)(ref string text, T t) {
    bool delegate(string) matchdg;
    int delid = -1;
    scope(exit) if (delid != -1)
      synchronized(ardlock) freeRuleData(delid);
    static if (T.length && is(T[0]: char[])) {
      alias T[1..$] Rest1;
      matchdg = matchrule(t[0], delid);
      auto rest1 = t[1..$];
    } else static if (T.length && is(T[0] == bool delegate(string))) {
      alias T[1..$] Rest1;
      matchdg = t[1];
      auto rest1 = t[1..$];
    } else {
      matchdg = cur;
      alias T Rest1;
      alias t rest1;
    }
    
    static if (Rest1.length && is(typeof(rest1[$-1](null))) && !is(Ret!(Rest1[$-1]) == void)) {
      static assert(is(typeof(rest1[$-1](null)) == bool) || is(typeof(rest1[$-1](null)) == ParseCtl),
        "Bad accept return type: "~typeof(rest1[$-1](null)).stringof);
      static assert(is(typeof(cast(Params!(Rest1[$-1])[0]) new Object)), "Bad accept params: "~Params!(Rest1[$-1]).stringof);
      alias Params!(Rest1[$-1])[0] MustType;
      alias Rest1[0 .. $-1] Rest2;
      auto accept = rest1[$-1];
      auto rest2 = rest1[0 .. $-1];
      static if (Rest2.length == 1 && is(typeof(*rest2[0])))
        static assert(is(Params!(Rest1[$-1]) == Tuple!(typeof(*rest2[0]))), "ParseCb mismatch: "~Params!(Rest1[$-1]).stringof~" != "~Tuple!(typeof(*rest2[0])).stringof);
    } else {
      bool delegate(Object) accept;
      alias Rest1 Rest2;
      alias rest1 rest2;
    }
    
    static if (Rest2.length == 1 && is(typeof(*rest2[0])) && !is(MustType))
      alias typeof(*rest2[0]) MustType;
    static if (Rest2.length == 1 && is(Rest2[0] == delegate)) {
      alias Params!(Rest2[0])[0] MustType;
      auto callback = rest2[0];
    }
    auto myAccept = delegate ParseCtl(Object obj) {
      static if (is(MustType)) {
        auto casted = fastcast!(MustType) (obj);
      } else {
        auto casted = obj;
      }
      if (!casted) {
        // logln("Reject ", obj, "; doesn't match ", typeof(casted).stringof, ".");
        return ParseCtl.RejectCont(null/*Format(obj, " doesn't match ", typeof(casted).stringof)*/);
      }
      static if (is(typeof(accept(casted)) == bool)) {
        return (!accept || accept(casted))?ParseCtl.AcceptAbort:ParseCtl.RejectCont(Format("accept dg to bool returned false"));
      }
      static if (is(typeof(accept(casted)) == ParseCtl)) {
        return accept?accept(casted):ParseCtl.AcceptAbort;
      }
      return ParseCtl.AcceptAbort;
    };
    
    static if (Rest2.length == 1 && is(typeof(*rest2[0])) || is(typeof(callback))) {
      // only accept-test objects that match the type
      auto backup = text;
      static if (is(typeof(callback))) {
        auto res = fastcast!(MustType) (dg(text, matchdg, myAccept));
        if (delid != -1) {
          synchronized(ardlock)
            freeRuleData(delid);
          delid = -1;
        }
        if (!res) text = backup;
        else callback(res);
        return fastcast!(Object) (res);
      } else {
        *rest2[0] = fastcast!(typeof(*rest2[0])) (dg(text, matchdg, myAccept));
        if (!*rest2[0]) text = backup;
        return fastcast!(Object) (*rest2[0]);
      }
    } else {
      static assert(!Rest2.length, "Left: "~Rest2.stringof~" of "~T.stringof);
      return dg(text, matchdg, myAccept);
    }
  }
}

class Parser {
  string key, id; // quickly exclude invalid matches
  Object match(ref string text, ParseCtl delegate(Object) accept, ParseCb cont, ParseCb restart) { assert(false); }
}

// stuff that it's unsafe to memoize due to side effects
bool delegate(string)[] globalStateMatchers;

void delegate()[] _pushCache, _popCache;

void pushCache() {
  foreach (dg; _pushCache) dg();
}

void popCache() {
  foreach (dg; _popCache) dg();
}

template DefaultParserImpl(alias Fn, string Id, bool Memoize, string Key) {
  final class DefaultParserImpl : Parser {
    bool dontMemoMe;
    this() {
      key = Key;
      id = Id;
      foreach (dg; globalStateMatchers) 
        if (dg(Id)) { dontMemoMe = true; break; }
      _pushCache ~= this /apply/ (typeof(this) that) {
        that.stack ~= that.cache;
        that.cache = Init!(typeof(that.cache));
      };
      _popCache ~= this /apply/ (typeof(this) that) {
        that.cache = that.stack[$-1];
        that.stack = that.stack[0 .. $-1];
      };
    }
    Object fnredir(ref string text, ParseCtl delegate(Object) accept, ParseCb cont, ParseCb rest) {
      static if (is(typeof((&Fn)(text, accept, cont, rest))))
        return Fn(text, accept, cont, rest);
      else
        return Fn(text, cont, rest);
    }
    static if (!Memoize) {
      override Object match(ref string text, ParseCtl delegate(Object) accept, ParseCb cont, ParseCb rest) {
        return fnredir(text, accept, cont, rest);
      }
    } else {
      // Stuple!(Object, char*)[char*] cache;
      SpeedCache cache;
      typeof(cache)[] stack;
      override Object match(ref string text, ParseCtl delegate(Object) accept, ParseCb cont, ParseCb rest) {
        auto t2 = text;
        if (.accept(t2, "]")) return null; // never a valid start
        static if (Key) {
          if (!.accept(t2, Key)) return null;
        }
        bool acceptRelevant;
        static if (is(typeof((&Fn)(t2, accept, cont, rest))))
          acceptRelevant = true;
        acceptRelevant &= !!accept;
        if (acceptRelevant || dontMemoMe) {
          auto res = fnredir(t2, accept, cont, rest);
          if (res) text = t2;
          return res;
        }
        auto ptr = t2.ptr;
        if (auto p = ptr in cache) {
          text = p._1[0 .. t2.ptr + t2.length - p._1];
          return p._0;
        }
        auto res = fnredir(t2, accept, cont, rest);
        cache[ptr] = stuple(res, t2.ptr);
        if (res) text = t2;
        return res;
      }
    }
  }
}

import tools.threads, tools.compat: rfind;
ParseContext parsecon;
static this() { New(parsecon); }

template DefaultParser(alias Fn, string Id, string Prec = null, string Key = null, bool Memoize = true) {
  static this() {
    static if (Prec) parsecon.addParser(new DefaultParserImpl!(Fn, Id, Memoize, Key), Prec);
    else parsecon.addParser(new DefaultParserImpl!(Fn, Id, Memoize, Key));
  }
}

import tools.log;
struct SplitIter(T) {
  T data, sep;
  T front, frontIncl, all;
  T pop() {
    for (int i = 0; i <= cast(int) data.length - cast(int) sep.length; ++i) {
      if (data[i .. i + sep.length] == sep) {
        auto res = data[0 .. i];
        data = data[i + sep.length .. $];
        front = all[0 .. $ - data.length - sep.length - res.length];
        frontIncl = all[0 .. front.length + res.length];
        return res;
      }
    }
    auto res = data;
    data = null;
    front = null;
    frontIncl = all;
    return res;
  }
}

SplitIter!(T) splitIter(T)(T d, T s) {
  SplitIter!(T) res;
  res.data = d; res.sep = s;
  res.all = res.data;
  return res;
}

void delegate(string) justAcceptedCallback;

class ParseContext {
  Parser[] parsers;
  string[string] prec; // precedence mapping
  void addPrecedence(string id, string val) { synchronized(this) { prec[id] = val; } }
  string lookupPrecedence(string id) {
    synchronized(this)
      if (auto p = id in prec) return *p;
    return null;
  }
  import tools.compat: split, join;
  string dumpInfo() {
    resort;
    string res;
    int maxlen;
    foreach (parser; parsers) {
      auto id = parser.id;
      if (id.length > maxlen) maxlen = id.length;
    }
    auto reserved = maxlen + 2;
    string[] prevId;
    foreach (parser; parsers) {
      auto id = parser.id;
      auto n = id.dup.split(".");
      foreach (i, str; n[0 .. min(n.length, prevId.length)]) {
        if (str == prevId[i]) foreach (ref ch; str) ch = ' ';
      }
      prevId = id.split(".");
      res ~= n.join(".");
      if (auto p = id in prec) {
        for (int i = 0; i < reserved - id.length; ++i)
          res ~= " ";
        res ~= ":" ~ *p;;
      }
      res ~= "\n";
    }
    return res;
  }
  bool idSmaller(Parser pa, Parser pb) {
    auto a = splitIter(pa.id, "."), b = splitIter(pb.id, ".");
    string ap, bp;
    while (true) {
      ap = a.pop(); bp = b.pop();
      if (!ap && !bp) return false; // equal
      if (ap && !bp) return true; // longer before shorter
      if (bp && !ap) return false;
      if (ap == bp) continue; // no information here
      auto aprec = lookupPrecedence(a.frontIncl), bprec = lookupPrecedence(b.frontIncl);
      if (!aprec && bprec)
        throw new Exception("Patterns "~a.frontIncl~" vs. "~b.frontIncl~": first is missing precedence info! ");
      if (!bprec && aprec)
        throw new Exception("Patterns "~a.frontIncl~" vs. "~b.frontIncl~": second is missing precedence info! ");
      if (!aprec && !bprec) return ap < bp; // lol
      if (aprec == bprec) throw new Exception("Error: patterns '"~a.frontIncl~"' and '"~b.frontIncl~"' have the same precedence! ");
      for (int i = 0; i < min(aprec.length, bprec.length); ++i) {
        // precedence needs to be _inverted_, ie. lower-precedence rules must come first
        // this is because "higher-precedence" means it binds tighter.
        // if (aprec[i] > bprec[i]) return true;
        // if (aprec[i] < bprec[i]) return false;
        if (aprec[i] < bprec[i]) return true;
        if (aprec[i] > bprec[i]) return false;
      }
      bool flip;
      // this gets a bit hairy
      // 50 before 5, 509 before 5, but 51 after 5.
      if (aprec.length < bprec.length) { swap(aprec, bprec); flip = true; }
      if (aprec[bprec.length] != '0') return flip;
      return !flip;
    }
  }
  void addParser(Parser p) {
    parsers ~= p;
    listModified = true;
  }
  void addParser(Parser p, string pred) {
    addParser(p);
    addPrecedence(p.id, pred);
  }
  import quicksort;
  bool listModified;
  void resort() {
    if (listModified) { // NOT in addParser - precedence info might not be registered yet!
      parsers.qsort(&idSmaller);
      listModified = false;
    }
  }
  Object parse(ref string text, bool delegate(string) cond,
      ParseCtl delegate(Object) accept) {
    return parse(text, cond, 0, accept);
  }
  string condStr;
  import tools.time: sec;
  Object parse(ref string text, bool delegate(string) cond,
      int offs = 0, ParseCtl delegate(Object) accept = null) {
    if (!text.length) return null;
    resort;
    bool matched;
    string xmlmark(string x) {
      return x.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace("'", "?");
    }
    if (verboseParser)
      logln("BEGIN PARSE '", text.nextText(16).xmlmark(), "'");
    
    ubyte[RULEPTR_SIZE_HAX] cond_copy = void;
    ParseCb cont = void, rest = void;
    cont.dg = null; // needed for null check further in
    int i;
    Object cont_dg(ref string text, bool delegate(string) cond, ParseCtl delegate(Object) accept) {
      return this.parse(text, cond, offs + i + 1, accept);
    }
    Object rest_dg(ref string text, bool delegate(string) cond, ParseCtl delegate(Object) accept) {
      return this.parse(text, cond, accept);
    }
    void fill_cont_rest() {
      // make copy
      cond_copy[] = (cast(ubyte*) cond.ptr)[0 .. RULEPTR_SIZE_HAX];
      cond.ptr = cond_copy.ptr;
      cont.dg = &cont_dg;
      cont.cur = cond;
      rest.dg = &rest_dg;
      rest.cur = cond;
    }
    
    Object longestMatchRes;
    string longestMatchStr = text;
    /*auto start_time = sec();
    auto start_text = text;
    static float min_speed = float.infinity;
    scope(exit) if (text.ptr !is start_text.ptr) {
      auto delta = (sec() - start_time) * 1000;
      auto speed = (text.ptr - start_text.ptr) / delta;
      if (speed < min_speed) {
        min_speed = speed;
        if (delta > 5) logln("New worst slowdown: '",
          condStr, "' at '", start_text.nextText(), "'"
          ": ", speed, " characters/ms "
          "(", (text.ptr - start_text.ptr), " in ", delta, "ms). ");
      }
      min_speed *= 1.01;
    }*/
    bool tried;
    foreach (j, parser; parsers[offs .. $]) {
      i = j;
      auto id = parser.id;
      
      auto tx = text;
      if (parser.key && !.accept(tx, parser.key)) continue; // skip
      
      // rulestack ~= stuple(id, text);
      // scope(exit) rulestack = rulestack[0 .. $-1];
      
      string xid() { return id.replace(".", "_"); }
      if (verboseXML) logln("<", xid, " text='", text.nextText(16).xmlmark(), "'>");
      scope(failure) if (verboseXML) logln("Exception</", xid, ">");
      if (cond(id)) {
        if (verboseParser) logln("TRY PARSER [", id, "] for '", text.nextText(16), "'");
        matched = true;
        
        if (!cont.dg) fill_cont_rest();
        
        auto backup = text;
        if (auto res = parser.match(text, accept, cont, rest)) {
          auto ctl = ParseCtl.AcceptAbort;
          if (accept) {
            ctl = accept(res);
            if (verboseParser) logln("    PARSER [", id, "]: control flow ", ctl.decode);
            if (ctl == ParseCtl.RejectAbort || ctl.state == 3) {
              if (verboseParser) logln("    PARSER [", id, "] rejected (", ctl.reason, "): ", Format(res));
              // if (verboseParser) logln("    PARSER [", id, "] @", rulestack /map/ ex!("a, b -> a"));
              if (verboseXML) logln("Reject</", xid, ">");
              text = backup;
              if (ctl == ParseCtl.RejectAbort) return null;
              continue;
            }
          }
          if (verboseParser) logln("    PARSER [", id, "] succeeded with ", res, ", left '", text.nextText(16), "'");
          if (verboseXML) logln("Success</", xid, ">");
          if (ctl == ParseCtl.AcceptAbort) {
            if (justAcceptedCallback) justAcceptedCallback(text);
            return res;
          }
          if (text.ptr > longestMatchStr.ptr) {
            longestMatchStr = text;
            longestMatchRes = res;
          }
        } else {
          if (verboseParser) logln("    PARSER [", id, "] failed");
          if (verboseXML) logln("Fail</", xid, ">");
        }
        text = backup;
      }/* else {
        if (verboseParser) logln("   PARSER [", id, "] - refuse outright");
        if (verboseXML) logln("Ignore</", xid, ">");
      }*/
    }
    if (longestMatchRes) {
      text = longestMatchStr;
      if (justAcceptedCallback) justAcceptedCallback(text);
      return longestMatchRes;
    }
    return null;
  }
  Object parse(ref string text, string cond) {
    condStr = cond;
    scope(exit) condStr = null;
    int delid = -1;
    scope(exit) if (delid != -1)
      synchronized(ardlock) freeRuleData(delid);
    try return parse(text, matchrule(cond, delid));
    catch (ParseEx pe) { pe.addRule(cond); throw pe; }
    catch (Exception ex) throw new Exception(Format("Matching rule '"~cond~"': ", ex));
  }
}

bool test(T)(T t) { if (t) return true; else return false; }

string getHeredoc(ref string text) {
  if (!text.accept("<<"))
    text.failparse("Expected heredoc");
  string sep;
  if (!text.gotIdentifier(sep))
    text.failparse("Could not get heredoc separator");
  return text.slice(sep);
}

pragma(attribute, hot)
template startsWith(S, T) {
  string startsWith(S text, T match)
  {
    if (text.length < match.length) return null;
    if (text[0 .. match.length] != match) return null;
    return text[match.length .. $];
  }
}
string cleanup(string s) {
  return s.replace("-", "_dash_");
}
