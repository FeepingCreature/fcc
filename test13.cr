module test13;

void main() {
  int foo;
  template test(T) <<EOF
    void test(T t) writeln "hi - $(string-of T) is $t, and foo $(++foo)";
  EOF
  test 5;
  test "hi";
}
