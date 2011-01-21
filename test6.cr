module test6;

int add (int a = 3, b = 5) { return a + b; }

void main() { writeln "forble $(add b=>7)"; }
