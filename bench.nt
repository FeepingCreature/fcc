module bench;

void main() {
  alias max = 10_000_000;
  auto l = 0 .. max;
  auto l2 = [for a <- l: double:a / 2];
  auto l3 = [for a <- l2: a + 2];
  auto v = sum l3;
  writeln "$v";
}
