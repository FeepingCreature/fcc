module ast.float_literal;

import ast.base;

bool gotFloat(ref string text, ref float f) {
  auto t2 = text;
  int i;
  if (!t2.gotInt(i)) return false;
  f = i;
  if (!t2.length || t2[0] != '.') return false;
  t2.take();
  float weight = 0.1;
  bool gotDigit;
  while (t2.length) {
    auto digit = t2[0];
    if (digit < '0' || digit > '9') break;
    gotDigit = true;
    int d = t2.take() - '0';
    if (f < 0) f -= weight * d;
    else f += weight * d;
    weight /= 10;
  }
  if (!gotDigit) return false;
  text = t2;
  return true;
}
