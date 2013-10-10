module ast.stringparse;

import ast.base, parseBase;

string filterEscapes(string s) {
  auto backup = s;
  ubyte[] res;
  byte xtake() {
    if (!s.length) fail;
    auto res = (cast(byte[]) s)[0];
    s = cast(string) (cast(byte[]) s)[1..$];
    return res;
  }
  bool purestr = true;
  while (s.length) {
    auto ch = xtake();
    if (ch == '\\') {
      purestr = false;
      auto ch2 = xtake();
      if (ch2 == 'n') { res ~= cast(ubyte[]) "\n"; }
      else if (ch2 == 'r') { res ~= cast(ubyte[]) "\r"; }
      else if (ch2 == 't') { res ~= cast(ubyte[]) "\t"; }
      else if (ch2 == 'x') {
        int h2i(char c) {
          if (c >= '0' && c <= '9') return c - '0';
          if (c >= 'a' && c <= 'f') return c - 'a' + 10;
          if (c >= 'A' && c <= 'F') return c - 'A' + 10;
          assert(false);
        }
        auto h1 = xtake(), h2 = xtake(); 
        res ~= h2i(h1) * 16 + h2i(h2);
      } else res ~= ch2;
    } else res ~= ch;
  }
  if (purestr) { delete res; return backup; }
  return cast(string) res;
}

bool gotString(ref string text, ref string res,
  string sep = "\""[], bool alreadyMatched = false, bool ignoreRes = false, bool doFilterEscapes = true)
{
  auto t2 = text;
  if (!alreadyMatched && !t2.accept(sep)) return false;
  auto stringstart = t2;
  
  if (sep == "`") doFilterEscapes = false;
  if (sep.length != 1) fail;
  
  int matchlength;
  byte xtake() {
    auto res = (cast(byte[]) t2)[0];
    t2 = cast(string) (cast(byte[]) t2)[1..$];
    matchlength ++;
    return res;
  }
  
  while (true) {
    if (!t2.length) return false;
    // if (t2.accept(sep)) break; // eats comments in strings
    if (auto rest = t2.startsWith(sep)) { t2 = rest; break; }
    auto ch = xtake();
    if (ch == '\\' && sep != "`") {
      auto ch2 = xtake();
    }
  }
  string str = stringstart[0..matchlength];
  if (str.ptr + str.length + 1 !is t2.ptr) fail;
  if (!ignoreRes) {
    res = str;
    if (doFilterEscapes) res = res.filterEscapes();
  }
  text = t2;
  return true;
}

bool canCoarseLexScope(string text) {
  // eat a number of plain identifiers such as "using mode GL"
  string id;
  while (text.gotIdentifier(id)) { }
  if (text.accept("{"[])) return true;
  else return false;
}

string coarseLexScope(ref string text, bool forceMatch = false, bool includeBrackets = true) {
  string local = text;
  if (includeBrackets) {
    // see canCoarseLexScope
    string ident;
    while (local.gotIdentifier(ident)) { }
  }
  if (!local.accept("{"[])) {
    if (forceMatch)
      local.failparse("COARSE: Opening bracket expected !"[]);
    return null;
  }
  if (!includeBrackets) text = local;
  int depth = 1;
  while (depth) {
    while (local.length && local[0] == '/') { auto backup = local; local.eatComments(); if (local is backup) break; }
    if (!local.length) text.failparse("COARSE: Unbalanced {}! "[]);
    auto ch = local[0];
    local = local[1..$];
    if (ch == '{') depth++;
    else if (ch == '}') depth--;
    else if (ch == '"') {
      string bogus;
      if (!gotString(local, bogus, "\""[], true, true))
        if (forceMatch) local.failparse("COARSE: Couldn't match string! "[]);
        else return null;
    } else if (ch == '`') {
      string bogus;
      if (!gotString(local, bogus, "`"[], true, true))
        if (forceMatch) local.failparse("COARSE: Couldn't match literal string! "[]);
        else return null;
    }
  }
  auto res = text[0..local.ptr - text.ptr];
  if (!includeBrackets) res = res[0..$-1];
  text = local;
  return res;
}
