module parseBase;

import tools.base;
enum Scheme { Binary, Octal, Decimal, Hex }
bool gotInt(ref string text, out int i) {
  auto t2 = text.strip();
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
    int[4] factor = [2, 8, 10, 16];
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

bool isAlpha(dchar d) {
  // TODO expand
  return d >= 'A' && d <= 'Z' || d >= 'a' && d <= 'z';
}

bool isAlphanum(dchar d) {
  return isAlpha(d) || d >= '0' && d <= '9';
}

import tools.compat: replace, strip;
import tools.base: Stuple, stuple;

string next_text(string s, int i = 100) {
  if (s.length > i) s = s[0 .. i];
  return s.replace("\n", "\\");
}

void eatComments(ref string s) {
  s = s.strip();
  while (true) {
    if (auto rest = s.startsWith("/*")) { rest.slice("*/"); s = rest.strip(); }
    else if (auto rest = s.startsWith("//")) { rest.slice("\n"); s = rest.strip(); }
    else break;
  }
}

bool accept(ref string s, string t) {
  auto s2 = s.strip();
  bool sep = t.length && t[$-1] == ' ';
  t = t.strip();
  s2.eatComments();
  // logln("accept ", t, " from ", s2.next_text(), "? ", !!s2.startsWith(t));
  return s2.startsWith(t) && (s = s2[t.length .. $], true) && (
    !sep || !s.length || s[0] == ' ' && (s = s[1 .. $], true)
  );
}

bool mustAccept(ref string s, string t, string err) {
  if (s.accept(t)) return true;
  throw new Exception(err);
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

bool gotIdentifier(ref string text, out string ident, bool acceptDots = false) {
  auto t2 = text.strip();
  t2.eatComments();
  bool isValid(char c) {
    return isAlphanum(c) || "_".find(c) != -1 || (acceptDots && c == '.');
  }
  if (!t2.length || !isValid(t2[0])) return false;
  auto identlen = 0, backup = t2;
  do {
    t2.take();
    identlen ++;
  } while (t2.length && isValid(t2[0]));
  ident = backup[0 .. identlen];
  text = t2;
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

alias Tuple!(bool, bool, bool, bool, bool, string, bool delegate(string), bool)
  RuleData;

const RULEPTR_SIZE_HAX = (Stuple!(RuleData)).sizeof;
void[] slab;

struct RuleStruct(alias A) {
  RuleData tuple;
  bool fun(Params!(typeof(&A))[RuleData.length .. $] rest) {
    return A(tuple, rest);
  }
}

template allocRuleData(alias A) {
  bool delegate(Params!(typeof(&A))[RuleData.length .. $])
  allocRuleData(RuleData rd) {
    if (!slab.length)
      slab = new void[RULEPTR_SIZE_HAX * 1024];
    auto res = slab.take(RULEPTR_SIZE_HAX);
    foreach (i, v; rd)
      (cast(Stuple!(RuleData)*) res.ptr).tupleof[i] = v;
    auto strp = cast(RuleStruct!(A)*) res.ptr;
    return &strp.fun;
  }
}

bool sectionStartsWith(string section, string rule) {
  if (section == rule) return true;
  auto match = section.startsWith(rule);
  // only count hits that match a complete section
  return match.length && match[0] == '.';
}

bool delegate(string) matchrule(string rules) {
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
    
    static bool fun(bool smaller, bool greater, bool equal,
    bool before, bool after,
    string rule, bool delegate(string) op1, ref bool hit, string text) {
      if (op1 && !op1(text)) return false;
      // avoid allocation from ~"."
      if (smaller && text.sectionStartsWith(rule)) // all "below" in the tree
        return true;
      if (equal && text == rule)
        return true;
      if (greater && !text.sectionStartsWith(rule)) // arguable
        return true;
      
      if (before) {
        if (text.sectionStartsWith(rule))
          hit = true;
        return !hit;
      }
      if (after) {
        if (text.sectionStartsWith(rule))
          hit = true;
        else return hit;
      }
      return false;
    };
    alias allocRuleData!(fun) ard;
    res = ard(smaller, greater, equal, before, after, rule, res, false);
    // res = res /apply/ (bool delegate(string) dg, string s) { auto res = dg(s); logln(s, " -> ", res); return res; };
  }
  // condInfo[res] = rules_backup;
  return res;
}

enum ParseCtl { AcceptAbort, RejectAbort, AcceptCont, RejectCont }
const ParseCtlDecode = ["AcceptAbort", "RejectAbort", "AcceptCont", "RejectCont"];

struct ParseCb {
  Object delegate(ref string text,
    bool delegate(string),
    ParseCtl delegate(Object) accept
  ) dg;
  bool delegate(string) cur; string curstr;
  string selfrule;
  void delegate() blockMemo;
  Object opCall(T...)(ref string text, T t) {
    bool delegate(string) matchdg;
    static if (T.length && is(T[0]: char[])) {
      alias T[1..$] Rest1;
      matchdg = matchrule = t[0].replace("selfrule", selfrule);
      auto rest1 = t[1..$];
    } else static if (T.length && is(T[0] == bool delegate(string))) {
      alias T[1..$] Rest1;
      matchdg = t[1];
      auto rest1 = t[1..$];
    } else {
      matchdg = cur;
      alias T Rest1;
      alias t rest1;
      // TODO: check if really necessary
      // blockMemo(); // callback depends on a parent's filter rule. cannot reliably memoize.
    }
    
    static if (Rest1.length && is(Rest1[$-1] == delegate) && !is(Ret!(Rest1[$-1]) == void)) {
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
    ParseCtl delegate(Object) myAccept;
    if (accept) myAccept = delegate ParseCtl(Object obj) {
      static if (is(MustType)) {
        auto casted = cast(MustType) obj;
      } else {
        auto casted = obj;
      }
      if (!casted) {
        // logln("Reject ", obj, "; doesn't match ", typeof(casted).stringof, ".");
        return ParseCtl.RejectCont;
      }
      static if (is(typeof(accept(casted)) == bool)) {
        return accept(casted)?ParseCtl.AcceptAbort:ParseCtl.RejectCont;
      }
      static if (is(typeof(accept(casted)) == ParseCtl)) {
        return accept(casted);
      }
      return ParseCtl.AcceptAbort;
    };
    
    static if (Rest2.length == 1 && is(typeof(*rest2[0])) || is(typeof(callback))) {
      // only accept-test objects that match the type
      auto backup = text;
      static if (is(typeof(callback))) {
        auto res = cast(MustType) dg(text, matchdg, myAccept);
        if (!res) text = backup;
        else callback(res);
        return cast(Object) res;
      } else {
        *rest2[0] = cast(typeof(*rest2[0])) dg(text, matchdg, myAccept);
        if (!*rest2[0]) text = backup;
        return cast(Object) *rest2[0];
      }
    } else {
      static assert(!Rest2.length, "Left: "~Rest2.stringof~" of "~T.stringof);
      return dg(text, matchdg, myAccept);
    }
  }
}

interface Parser {
  string getId();
  Object match(ref string text, ParseCtl delegate(Object) accept, ParseCb cont, ParseCb restart);
  void blockNextMemo();
}

// stuff that it's unsafe to memoize due to side effects
bool delegate(string)[] globalStateMatchers;

template DefaultParserImpl(alias Fn, string Id, bool Memoize) {
  class DefaultParserImpl : Parser {
    bool dontMemoMe;
    this() {
      foreach (dg; globalStateMatchers) 
        if (dg(Id)) { dontMemoMe = true; break; }
    }
    override string getId() { return Id; }
    bool doBlock;
    override void blockNextMemo() {
      if (verboseParser) logln("Block ", Id, " memo due to pass-through cont/next");
      doBlock = true;
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
      Stuple!(Object, string) [char*] cache;
      override Object match(ref string text, ParseCtl delegate(Object) accept, ParseCb cont, ParseCb rest) {
        bool acceptRelevant;
        static if (is(typeof((&Fn)(text, accept, cont, rest))))
          acceptRelevant = true;
        acceptRelevant &= !!accept;
        if (acceptRelevant || dontMemoMe) return fnredir(text, accept, cont, rest);
        auto ptr = text.ptr;
        if (auto p = ptr in cache) {
          text = p._1;
          return p._0;
        }
        auto res = fnredir(text, accept, cont, rest);
        if (!doBlock) cache[ptr] = stuple(res, text);
        // else logln("Memoization blocked! ");
        doBlock = false;
        return res;
      }
    }
  }
}

import tools.threads, tools.compat: rfind;
ParseContext parsecon;
static this() { New(parsecon); }

template DefaultParser(alias Fn, string Id, string Prec = null, bool Memoize = true) {
  static this() {
    static if (Prec) parsecon.addParser(new DefaultParserImpl!(Fn, Id, Memoize), Prec);
    else parsecon.addParser(new DefaultParserImpl!(Fn, Id, Memoize));
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
      auto id = parser.getId();
      if (id.length > maxlen) maxlen = id.length;
    }
    auto reserved = maxlen + 2;
    string[] prevId;
    foreach (parser; parsers) {
      auto id = parser.getId();
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
    auto a = splitIter(pa.getId(), "."), b = splitIter(pb.getId(), ".");
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
    addPrecedence(p.getId(), pred);
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
  Object parse(ref string text, bool delegate(string) cond,
      int offs = 0, ParseCtl delegate(Object) accept = null) {
    resort;
    bool matched;
    string xmlmark(string x) {
      return x.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace("'", "?");
    }
    if (verboseParser)
      logln("BEGIN PARSE '", text.next_text(16).xmlmark(), "'");
    
    // make copy
    ubyte[RULEPTR_SIZE_HAX] cond_copy =
      (cast(ubyte*) cond.ptr)[0 .. RULEPTR_SIZE_HAX];
    cond.ptr = cond_copy.ptr;
    
    Object longestMatchRes;
    string longestMatchStr = text;
    foreach (i, parser; parsers[offs .. $]) {
      auto id = parser.getId();
      string xid() { return id.replace(".", "_"); }
      if (verboseXML) logln("<", xid, " text='", text.next_text(16).xmlmark(), "'>");
      scope(failure) if (verboseXML) logln("Exception</", xid, ">");
      if (cond(id)) {
        if (verboseParser) logln("TRY PARSER [", id, "] for '", text.next_text(16), "'");
        matched = true;
        ParseCb cont, rest;
        cont.dg = (ref string text, bool delegate(string) cond,
          ParseCtl delegate(Object) accept) {
          return this.parse(text, cond, offs + i + 1, accept);
        };
        cont.cur = cond;
        cont.curstr = id;
        cont.selfrule = id;
        cont.blockMemo = &parser.blockNextMemo;
        
        rest.dg = (ref string text, bool delegate(string) cond,
          ParseCtl delegate(Object) accept) {
          return this.parse(text, cond, accept);
        };
        rest.cur = cond;
        rest.curstr = id;
        rest.selfrule = id;
        rest.blockMemo = &parser.blockNextMemo;
        
        auto backup = text;
        if (auto res = parser.match(text, accept, cont, rest)) {
          auto ctl = ParseCtl.AcceptAbort;
          if (accept) {
            ctl = accept(res);
            if (verboseParser) logln("    PARSER [", id, "]: control flow ", ParseCtlDecode[ctl]);
            if (ctl == ParseCtl.RejectAbort || ctl == ParseCtl.RejectCont) {
              if (verboseParser) logln("    PARSER [", id, "] rejected ", Format(res));
              if (verboseXML) logln("Reject</", xid, ">");
              text = backup;
              if (ctl == ParseCtl.RejectAbort) return null;
              continue;
            }
          }
          if (verboseParser) logln("    PARSER [", id, "] succeeded with ", res, ", left '", text.next_text(16), "'");
          if (verboseXML) logln("Success</", xid, ">");
          if (ctl == ParseCtl.AcceptAbort) return res;
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
      return longestMatchRes;
    }
    // okay to not match anything if we're just continuing
    if (!offs && !matched) {
      string[] ids; foreach (parser; parsers) ids ~= parser.getId();
      logln("Parsers: ", ids);
      if (condStr) throw new Exception(Format(
        "Found no patterns to match condition \"", condStr, "\" after ", offs
      ));
      else throw new Exception(Format(
        "Found no patterns to match condition after ", offs
      ));
    }
    return null;
  }
  Object parse(ref string text, string cond) {
    condStr = cond;
    scope(exit) condStr = null;
    try return parse(text, matchrule=cond);
    catch (Exception ex) throw new Exception(Format("Matching rule '"~cond~"': ", ex));
  }
}

bool test(T)(T t) { if (t) return true; else return false; }

string getHeredoc(ref string text) {
  if (!text.accept("<<")) throw new Exception("Expected heredoc, got '"~text.next_text()~"'");
  string sep;
  if (!text.gotIdentifier(sep)) throw new Exception("Could not get heredoc separator at '"~text.next_text()~"'");
  return text.slice(sep);
}

string startsWith(string text, string match) {
  if (!text) return null;
  if (!match) return text;
  if (text.length < match.length) return null;
  if (text[0 .. match.length] != match) return null;
  return text[match.length .. $];
}
