module test13;

import std.string;

struct Foo {
  int u;
  template bar(T) <<EOF
    void bar(T t) { writeln "Hi, bar here with $t and $u. "; }
  EOF
  template baz(alias A) <<EOF
    alias baz = mixin A.replace("%", "u");
  EOF
}

void main() {
  int foo;
  template test(T) <<EOF
    void test(T t) writeln "hi - $(string-of T) is $t, and foo $(++foo)";
  EOF
  test 5;
  test "hi";
  Foo foo2;
  foo2.u = 5;
  foo2.bar 8;
  auto res = foo2.baz!`%+2`;
  writeln "$res";
  auto vec = vec3f(2, 3, 4);
  vec = vec.ex!`%+2`;
  writeln "$(vec.(x, y, z))";
}
