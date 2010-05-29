module test;
import sys;

int add(int a, int b) { return a + b; }

void test(int foo) {
  int bar = 17;
  if (foo) sys.printf("meep\n");
  else sys.printf("moop\n");
  sys.printf("Hello World: %i, %i\n", foo * add(2, bar), bar);
  int temp = 5;
  while (temp) {
    sys.printf("Countdown with %i\n", temp);
    temp = temp - 1;
  }
  for (int x = 0; x < 10; ++x)
    sys.printf("Test: %i\n", x);
}

int acker(int m, int n) {
  if (m) {
    if (n) return acker(m - 1, acker(m, n - 1));
    else return acker(m - 1, 1);
  } else return n + 1;
}

/*
void test2(A a) {
  printf("A test: %i\n", a.x);
}

class A {
  int x;
}
*/

/*
  OO design rev1
  
*/

/*extend {
  bool gotExtC(ref string text, out NilStatement ns) {
    ns = new NilStatement;
    Type t;
    string id;
    return text.accept("extern(C)") && text.gotType(
  }
  this() {
    
  }
}*/

struct X {
  int a, b;
  int c;
}

struct Y {
  X x;
  int i;
}

int s(int i, int k) {
  printf("meep %i: %i\n", i, k);
  return k;
}

void main() {
  /*A a = new A;
  a.x = 5;
  test2(a);*/
  test(2);
  test(0);
  int e = 5;
  // printf("a(3, 12) = %i\n", acker(3, 12));
  int* ptr = &e;
  *ptr = 7;
  X x;
  x.a = 5; x.b = 6; x.c = 3;
  Y y;
  y.x = x;
  y.x.c = 5;
  printf("It's a %i! ", y.x.c);
  printf("yo .. %i, %i, %i\n", x.a, x.b, x.c);
  printf("pointer to e: %p. e: %i, also %i.\n", ptr, *ptr, *&*&e);
  int m = 5;
  int n = 8;
  printf("post inc test: %i, %i\n", m++, m++);
  printf("test: %i\n", *(&m - 1));
  if (s(0, 1) && s(1, 0) && s(2, 1)) printf("yes\n"); else printf("no\n");
  if (s(0, 1) && s(1, 0) && s(2, 1) || s(3, 1)) printf("yes\n"); else printf("no\n");
  int[5] ifield;
  ifield[3] = 15;
  printf("field access %i\n", ifield[3]);
  int* ip = &ifield[3];
  printf("field access via ptr %i\n", ip[0]);
}
