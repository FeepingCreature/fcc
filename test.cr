module test;
import sys;

int add(int a, int b) { return a + b; }

void test(int foo) {
  int bar = 17;
  if (foo) sys.printf("meep\n");
  else sys.printf("moop\n");
  sys.printf("Hello World: %i, %i\n", foo * add(2, bar), bar);
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

void main() {
  /*A a = new A;
  a.x = 5;
  test2(a);*/
  test(2);
  test(0);
}
