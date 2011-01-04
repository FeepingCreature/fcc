module bench;

void main() {
  alias max = 100_000_000;
  auto l = 0 .. max;
  auto l2 = [for a <- l: (float:a) / 2];
  auto l3 = [for a <- l2: a + 2];
  auto v = sum l3;
  writeln "$v";
}
