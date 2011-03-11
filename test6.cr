module test6;

int delegate(int)add (int a){return new delegate int(int b){return a+b;};}

void main() {
  int val = (add 2 3); /* look ma it's lisp */ writeln "forble $val";
  writeln "forble $(add b=>7)"; (int, float)[1] foo; writeln "mew $(string-of type-of foo)";
}
