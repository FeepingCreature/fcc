module errors;

import tools.base;

string nextText(string s, int i = 100) {
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

public import tools.threads: SyncObj;

string[string] sourcefiles;

// row, col, file
Stuple!(int, ptrdiff_t, string) lookupPos(string text) {
  eatComments(text);
  text = text.strip();
  synchronized(SyncObj!(sourcefiles)) foreach (key, value; sourcefiles) {
    // yes, >. Not >=. Think about it.
    if (text.ptr < value.ptr || text.ptr > value.ptr + value.length)
      continue;
    int i;
    while (value) {
      auto line = value.slice("\n");
      if (text.ptr < line.ptr || text.ptr > line.ptr + line.length) {
        i++;
        continue;
      }
      return stuple(i + 1, text.ptr - line.ptr, key.dup);
    }
    assert(false);
  }
  return stuple(0, cast(ptrdiff_t) 0, "<unknown>");
}

class ParseEx : Exception {
  string pos;
  string[] rules;
  this(string pos, string s) { this.pos = pos; super(s); }
  void addRule(string s) { rules ~= s; }
  string toString() {
    auto info = lookupPos(pos);
    if (info._2 == "<unknown>") info._2 = "@`"~pos.nextText()~"`";
    auto res = Format(info._2, ":", info._0, ":", info._1, ": ", msg);
    if (rules) res ~= Format(" ", rules);
    return res;
  } 
}

import tools.threads: TLS;
import tools.base: New;

// source, mesg
TLS!(Stuple!(string, string)) error;

void failparse(T...)(string text, T t) {
  auto str = Format(t);
  if (auto mesg = error()._1) str ~= ": "~mesg;
  throw new ParseEx(text, str);
}

static this() { New(error); }

void setError(T...)(string text, T t) {
  *error.ptr() = stuple(text, Format(t));
}

void passert(T...)(string text, bool b, T t) {
  if (!b) text.failparse(t);
}
