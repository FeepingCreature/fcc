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
  t = t.strip();
  s2.eatComments();
  // logln("accept ", t, " from ", s2.next_text(), "? ", !!s2.startsWith(t));
  return s2.startsWith(t) && (s = s2[t.length .. $], true);
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
    return isAlphanum(c) || (acceptDots && c == '.');
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

bool verboseParser = false;

bool delegate(string) matchrule(string rules) {
  bool delegate(string) res;
  while (rules.length) {
    auto rule = rules.slice(" ");
    res = stuple(rule, res) /apply/ (string rule, bool delegate(string) op1, string text) {
      if (op1 && !op1(text)) return false;
      
      bool smaller, greater, equal;
      if (auto rest = rule.startsWith("<")) { smaller = true; rule = rest; }
      if (auto rest = rule.startsWith(">")) { greater = true; rule = rest; }
      if (auto rest = rule.startsWith("=")) { equal = true; rule = rest; }
      
      if (!smaller && !greater && !equal)
        smaller = equal = true; // default
      
      // logln(smaller?"<":"", greater?">":"", equal?"=":"", " ", text, " against ", rule);
      auto tsw = text.startsWith(rule);
      // avoid allocation from ~"."
      if (smaller && tsw.length && tsw[0] == '.') // all "below" in the tree
        return true;
      if (equal && text == rule)
        return true;
      if (greater && !text.startsWith(rule)) // arguable
        return true;
      return false;
    };
  }
  return res;
}

struct ParseCb {
  Object delegate(ref string text,
    bool delegate(string),
    bool delegate(Object) accept
  ) dg;
  bool delegate(string) cur; string curstr;
  Object opCall(T...)(ref string text, T t) {
    bool delegate(string) matchdg;
    static if (T.length && is(T[0]: char[])) {
      alias T[1..$] Rest1;
      matchdg = matchrule = t[0];
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
    
    bool delegate(Object) accept;
    static if (Rest1.length && is(Rest1[$-1] == bool delegate(Object))) {
      alias Rest1[0 .. $-1] Rest2;
      accept = rest1[$-1];
      auto rest2 = rest1[0 .. $-1];
    } else {
      alias Rest1 Rest2;
      alias rest1 rest2;
    }
    
    static if (Rest2.length == 1 && is(typeof(*rest2[0]))) {
      *rest2[0] = cast(typeof(*rest2[0])) dg(text, matchdg, accept);
      return cast(Object) *rest2[0];
    } else {
      static assert(!Rest2.length, "Left: "~Rest2.stringof~" of "~T.stringof);
      return dg(text, matchdg, accept);
    }
  }
}

interface Parser {
  string getId();
  Object match(ref string text, ParseCb cont, ParseCb restart);
}

template DefaultParserImpl(alias Fn, string Id, bool Memoize) {
  class DefaultParserImpl : Parser {
    override string getId() { return Id; }
    static if (!Memoize) {
      override Object match(ref string text, ParseCb cont, ParseCb rest) {
        return Fn(text, cont, rest);
      }
    } else {
      Stuple!(Object, string) [char*] cache;
      override Object match(ref string text, ParseCb cont, ParseCb rest) {
        auto ptr = text.ptr;
        if (auto p = ptr in cache) {
          text = p._1;
          return p._0;
        }
        auto res = Fn(text, cont, rest);
        cache[ptr] = stuple(res, text);
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
      // 50 before 5, but 51 after 5.
      if (aprec.length < bprec.length) { swap(aprec, bprec); flip = true; }
      for (int i = bprec.length; i < aprec.length; ++i) {
        if (aprec[i] != '0') return flip;
      }
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
      bool delegate(Object) accept) {
    return parse(text, cond, 0, accept);
  }
  Object parse(ref string text, bool delegate(string) cond,
      int offs = 0, bool delegate(Object) accept = null) {
    resort;
    bool matched;
    if (verboseParser)
      logln("BEGIN PARSE '", text.next_text(16), "'");
    foreach (i, parser; parsers[offs .. $]) {
      if (cond(parser.getId())) {
        if (verboseParser) logln("TRY PARSER [", parser.getId(), "] for '", text.next_text(16), "'");
        matched = true;
        ParseCb cont, rest;
        cont.dg = (ref string text, bool delegate(string) cond,
          bool delegate(Object) accept) {
          return this.parse(text, cond, offs + i + 1, accept);
        };
        cont.cur = cond;
        cont.curstr = parser.getId();
        
        rest.dg = (ref string text, bool delegate(string) cond,
          bool delegate(Object) accept) {
          return this.parse(text, cond, accept);
        };
        rest.cur = cond;
        rest.curstr = parser.getId();
        
        auto t2 = text;
        if (auto res = parser.match(t2, cont, rest)) {
          if (accept) {
            if (accept(res)) {
              text = t2;
              if (verboseParser) logln("    PARSER [", parser.getId(), "] succeeded with ", res, ", left '", text.next_text(16), "'");
              return res;
            }
          } else {
            text = t2;
            if (verboseParser) logln("    PARSER [", parser.getId(), "] succeeded with ", res, ", left '", text.next_text(16), "'");
            return res;
          }
        }
        if (verboseParser) logln("    PARSER [", parser.getId(), "] failed");
      }
    }
    if (!matched) throw new Exception("Found no patterns to match condition! ");
    return null;
  }
  Object parse(ref string text, string cond) {
    try return parse(text, matchrule=cond);
    catch (Exception ex) throw new Exception(Format("Matching rule '"~cond~"': ", ex));
  }
}

bool test(T)(T t) { if (t) return true; else return false; }
