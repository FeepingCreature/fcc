module test7;

class A {
  void init() { }
  void init(int i) { }
  void init(float f) { }
  void whee() writeln "Whee";
}

void a(int i) { }
void a(float f) { }

void main() {
  a 4;
  a 4f;
  // a short:4;
  auto cl = new A;
  cl.init 4;
  cl.init 4f;
  auto cm = new A 4;
  auto cn = new A(5f);
  new A.whee();
}
