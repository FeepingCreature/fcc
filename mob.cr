module mob;

int delegate() lit(int i) { return new delegate int() { return i; }; }

void main() {
  int A(int k, int delegate() x1, x2, x3, x4, x5) {
    int B() {
      k --;
      return A(k, &B, x1, x2, x3, x4);
    }
    if (k <= 0) return x4() + x5();
    else return B();
  }
  auto res = A(10, lit 1, lit -1, lit -1, lit 1, lit 0);
  writeln "$res";
}
