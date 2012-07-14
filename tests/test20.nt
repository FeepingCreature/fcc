module test20;

struct Foo {
  int a;
  class InnerFoo {
    int b;
    void borz() { writeln "$(a+b)"; }
  }
  InnerFoo genif() { return new InnerFoo; }
}

class Bar {
  int a;
  class InnerBar {
    int b;
    void borz() { writeln "$(a+b)"; }
  }
  InnerBar genib() { return new InnerBar; }
}

void main() {
  Foo foo;
  foo.a = 5;
  // auto ifoo = foo.new Bar;
  // auto ifoo = new Foo.InnerFoo;
  auto ifoo = foo.genif();
  // ifoo.context = &foo;
  ifoo.b = 8;
  ifoo.borz();
  
  Bar bar = new Bar;
  bar.a = 6;
  // auto ibar = new Bar.InnerBar;
  auto ibar = bar.genib();
  // ibar.context = bar;
  ibar.b = 9;
  ibar.borz();
}
