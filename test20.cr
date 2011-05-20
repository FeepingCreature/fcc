module test20;

struct Foo {
  int a;
  class InnerFoo {
    int b;
    void borz() { writeln "$(a+b)"; }
  }
}

class Bar {
  int a;
  class InnerBar {
    int b;
    void borz() { writeln "$(a+b)"; }
  }
}

void main() {
  Foo foo;
  foo.a = 5;
  // auto ifoo = foo.new Bar;
  auto ifoo = new Foo.InnerFoo;
  ifoo.context = &foo;
  ifoo.b = 8;
  ifoo.borz();
  
  Bar bar = new Bar;
  bar.a = 6;
  auto ibar = new Bar.InnerBar;
  ibar.context = bar;
  ibar.b = 9;
  ibar.borz();
}
