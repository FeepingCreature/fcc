module ast.float_literal;

import ast.base;

bool gotDouble(ref string text, ref double d) {
  auto t2 = text;
  bool neg;
  t2.eatComments();
  if (t2.accept("-"[])) { neg = true; }
  d = 0;
  bool isDigit(char c) { return c >= '0' && c <= '9'; }
  while (t2.length) {
    if (t2[0] == '_') { t2.take(); continue; }
    auto digit = t2[0];
    if (!isDigit(digit)) break;
    t2.take();
    int dig = digit - '0';
    d = d * 10 + dig;
  }
  if (!t2.length || t2.take() != '.') return false;
  double weight = 0.1;
  bool gotDigit;
  while (t2.length) {
    auto digit = t2[0];
    if (digit < '0' || digit > '9') break;
    gotDigit = true;
    int dig = t2.take() - '0';
    d += weight * dig;
    weight /= 10;
  }
  if (!gotDigit) return false;
  if (neg) d = -d;
  text = t2;
  return true;
}

bool gotFloat(ref string text, ref float f) {
  double d; int i;
  auto t2 = text;
  if (t2.gotInt(i) && t2.takech(' ') == 'f') {
    text = t2; f = i;
    return true;
  }
  t2 = text;
  if (t2.gotDouble(d) && t2.takech(' ') == 'f') {
    text = t2; f = cast(float) d;
    return true;
  }
  return false;
}
