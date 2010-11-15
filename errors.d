module errors;

import tools.base;

string nextText(string s, int i = 100) {
  if (s.length > i) s = s[0 .. i];
  return s.replace("\n", "\\");
}

string[string] sourcefiles;

// row, col, file
Stuple!(int, int, string) lookupPos(string text) {
  foreach (key, value; sourcefiles) {
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
  return stuple(0, 0, "<unknown>");
}

class ParseEx : Exception {
  string pos;
  string[] rules;
  this(string pos, string s) { this.pos = pos; super(s); }
  void addRule(string s) { rules ~= s; }
  string toString() {
    auto info = lookupPos(pos);
    auto res = Format(info._2, ":", info._0, ":", info._1, ": ", msg);
    if (rules) res ~= Format(" ", rules);
    return res;
  } 
}

void failparse(T...)(string text, T t) {
  throw new ParseEx(text, Format(t));
}

// source, mesg
Stuple!(string, string) error; // TODO: tls

void setError(T...)(string text, T t) {
  error = stuple(text, Format(t));
}

void passert(T...)(string text, bool b, T t) {
  if (!b) text.failparse(t);
}
