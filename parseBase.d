module parseBase;

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
  bool isNum(char c) { return c >= '0' && c <= '9'; }
  if (!t2.length || !isNum(t2[0])) return false;
  int res = t2.take() - '0';
  while (t2.length) {
    if (!isNum(t2[0])) break;
    res = res * 10 + t2.take() - '0'; 
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
import tools.base;
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

bool bjoin(ref string s, lazy bool c1, lazy bool c2, void delegate() dg, bool allowEmpty = true) {
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
bool many(ref string s, lazy bool b, void delegate() dg = null) {
  while (true) {
    auto s2 = s;
    if (!b()) { s = s2; break; }
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
  do {
    ident ~= t2.take();
  } while (t2.length && isValid(t2[0]));
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

const RULEPTR_SIZE_HAX = (Stuple!(string, void delegate(), bool)).sizeof + (void delegate()).sizeof;

bool delegate(string) matchrule(string rules) {
  bool delegate(string) res;
  auto rules_backup = rules;
  while (rules.length) {
    auto rule = rules.slice(" ");
    res = stuple(rule, res, false) /apply/
    (string rule, bool delegate(string) op1, ref bool hit, string text) {
      if (op1 && !op1(text)) return false;
      
      bool smaller, greater, equal, before;
      if (auto rest = rule.startsWith("<")) { smaller = true; rule = rest; }
      if (auto rest = rule.startsWith(">")) { greater = true; rule = rest; }
      if (auto rest = rule.startsWith("=")) { equal = true; rule = rest; }
      if (auto rest = rule.startsWith("^")) { before = true; rule = rest; }
      
      if (!smaller && !greater && !equal && !before)
        smaller = equal = true; // default
      
      // different modes
      assert((smaller || greater || equal) ^ before);
      
      auto tsw = text.startsWith(rule);
      // avoid allocation from ~"."
      if (smaller && tsw.length && tsw[0] == '.') // all "below" in the tree
        return true;
      if (equal && text == rule)
        return true;
      if (greater && !text.startsWith(rule)) // arguable
        return true;
      
      if (before) {
        if (!hit && text.startsWith(rule))
          hit = true;
        if (hit) return false;
        return true;
      }
      return false;
    };
  }
  condInfo[res] = rules_backup;
  return res;
}

enum ParseCtl { AcceptAbort, RejectAbort, AcceptCont, RejectCont }

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
    
    static if (Rest1.length && is(Rest1[$-1] == delegate)) {
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
    ParseCtl delegate(Object) myAccept;
    if (accept) myAccept = delegate ParseCtl(Object obj) {
      static if (is(MustType)) {
        auto casted = cast(MustType) obj;
      } else {
        auto casted = obj;
      }
      if (!casted) {
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
    
    static if (Rest2.length == 1 && is(typeof(*rest2[0]))) {
      // only accept-test objects that match the type
      *rest2[0] = cast(typeof(*rest2[0])) dg(text, matchdg, myAccept);
      return cast(Object) *rest2[0];
    } else {
      static assert(!Rest2.length, "Left: "~Rest2.stringof~" of "~T.stringof);
      return dg(text, matchdg, myAccept);
    }
  }
}

interface Parser {
  string getId();
  Object match(ref string text, ParseCb cont, ParseCb restart);
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
    static if (!Memoize) {
      override Object match(ref string text, ParseCb cont, ParseCb rest) {
        return Fn(text, cont, rest);
      }
    } else {
      Stuple!(Object, string) [char*] cache;
      override Object match(ref string text, ParseCb cont, ParseCb rest) {
        if (dontMemoMe) return Fn(text, cont, rest);
        auto ptr = text.ptr;
        if (auto p = ptr in cache) {
          text = p._1;
          return p._0;
        }
        auto res = Fn(text, cont, rest);
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
    cond.ptr = (cast(ubyte*) cond.ptr)[0 .. RULEPTR_SIZE_HAX].dup.ptr;
    Object longestMatchRes;
    string longestMatchStr;
    foreach (i, parser; parsers[offs .. $]) {
      auto xid = parser.getId().replace(".", "_");
      if (verboseXML) logln("<", xid, " text='", text.next_text(16).xmlmark(), "'>");
      scope(failure) if (verboseXML) logln("Exception</", xid, ">");
      if (cond(parser.getId())) {
        if (verboseParser) logln("TRY PARSER [", parser.getId(), "] for '", text.next_text(16), "'");
        matched = true;
        ParseCb cont, rest;
        cont.dg = (ref string text, bool delegate(string) cond,
          ParseCtl delegate(Object) accept) {
          return this.parse(text, cond, offs + i + 1, accept);
        };
        cont.cur = cond;
        cont.curstr = parser.getId();
        cont.selfrule = parser.getId();
        cont.blockMemo = &parser.blockNextMemo;
        
        rest.dg = (ref string text, bool delegate(string) cond,
          ParseCtl delegate(Object) accept) {
          return this.parse(text, cond, accept);
        };
        rest.cur = cond;
        rest.curstr = parser.getId();
        rest.selfrule = parser.getId();
        rest.blockMemo = &parser.blockNextMemo;
        
        auto backup = text;
        if (auto res = parser.match(text, cont, rest)) {
          auto ctl = ParseCtl.AcceptAbort;
          if (accept) {
            ctl = accept(res);
            if (ctl == ParseCtl.RejectAbort || ctl == ParseCtl.RejectCont) {
              if (verboseParser) logln("    PARSER [", parser.getId(), "] rejected ", Format(res));
              if (verboseXML) logln("Reject</", xid, ">");
              text = backup;
              if (ctl == ParseCtl.RejectAbort) return null;
              continue;
            }
          }
          if (verboseParser) logln("    PARSER [", parser.getId(), "] succeeded with ", res, ", left '", text.next_text(16), "'");
          if (verboseXML) logln("Success</", xid, ">");
          if (ctl == ParseCtl.AcceptAbort) return res;
          if (text.ptr > longestMatchStr.ptr) {
            longestMatchStr = text;
            longestMatchRes = res;
          }
        } else {
          if (verboseParser) logln("    PARSER [", parser.getId(), "] failed");
          if (verboseXML) logln("Fail</", xid, ">");
        }
        text = backup;
      }/* else {
        if (verboseParser) logln("   PARSER [", parser.getId(), "] - refuse outright");
        if (verboseXML) logln("Ignore</", xid, ">");
      }*/
    }
    if (longestMatchStr) {
      text = longestMatchStr;
      return longestMatchRes;
    }
    // okay to not match anything if we're just continuing
    if (!offs && !matched)
      if (condStr) throw new Exception(Format(
        "Found no patterns to match condition \"", condStr, "\" after ", offs
      ));
      else throw new Exception(Format(
        "Found no patterns to match condition after ", offs
      ));
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
