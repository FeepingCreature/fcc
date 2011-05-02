module test19;

enum Test {
  A = 2, B, C = A + B
}

void main() { Test a = Test.A, b = Test.B, c = Test.C; writeln "a $a, b $b, c $c"; /*c = 6; fails as it should */ }
