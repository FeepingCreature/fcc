module test5;

import std.file;

void main() {
  auto mods = [for mod <- __modules: mod.name].eval;
  writeln "Modules: $mods";
}
