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
    else if (auto rest = s.startsWith("/+")) {
      int depth = 1;
      while (depth) {
        auto a = rest.find("/+"), b = rest.find("+/");
        if (b == -1)
          throw new Exception("Unbalanced comments! ");
        if (a != -1 && a < b) {
          depth++;
          rest = rest[a + 2 .. $];
          continue;
        }
        depth --;
        rest = rest[b + 2 .. $];
      }
      s = rest.strip();
    }
    else if (auto rest = s.startsWith("//")) { rest.slice("\n"); s = rest.strip(); }
    else break;
  }
}

public import tools.threads: SyncObj;

string[string] sourcefiles;

// progress, file
Stuple!(float, string) lookupProgress(string text) {
  eatComments(text);
  text = text.strip();
  synchronized(SyncObj!(sourcefiles)) foreach (key, value; sourcefiles) {
    // yes, >. Not >=. Think about it.
    if (text.ptr < value.ptr || text.ptr > value.ptr + value.length)
      continue;
    return stuple((text.ptr - value.ptr) * 1f / value.length, key.dup);
  }
  return stuple(0f, cast(string) null);
}

// row, col, file
Stuple!(int, ptrdiff_t, string, string) lookupPos(string text) {
  eatComments(text);
  text = text.strip();
  synchronized(SyncObj!(sourcefiles)) foreach (key, value; sourcefiles) {
    if (text.ptr < value.ptr || text.ptr > value.ptr + value.length)
      continue;
    int i;
    while (value) {
      auto line = value.slice("\n");
      if (text.ptr < line.ptr || text.ptr > line.ptr + line.length) {
        i++;
        continue;
      }
      return stuple(i + 1, text.ptr - line.ptr, key.dup, line);
    }
    assert(false);
  }
  return stuple(0, cast(ptrdiff_t) 0, "<unknown>", cast(string) null);
}

class ParseEx : Exception {
  string pos;
  string[] rules;
  this(string pos, string s) { this.pos = pos; super(s); }
  void addRule(string s) { rules ~= s; }
  string toString() {
    auto info = lookupPos(pos);
    if (info._2 == "<unknown>") info._2 = "@`"~pos.nextText()~"`";
    string res;
    if (info._3) {
      auto prefix = "At line: ";
      res = Format("\n", prefix, info._3, "\n");
      for (int i = 0; i < prefix.length + info._1; ++i)
        res ~= " ";
      res ~= "^\n";
    }
    
    res ~= Format(info._2, ":", info._0, ":", info._1, ": ", msg);
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

void resetError() {
  *error.ptr() = stuple(cast(string) null, cast(string) null);
}

void passert(T...)(string text, bool b, T t) {
  if (!b) text.failparse(t);
}
