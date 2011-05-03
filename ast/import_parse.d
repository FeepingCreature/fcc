module ast.import_parse;

import ast.base, parseBase, ast.slice, ast.static_arrays, ast.fold, ast.literal_string;
import std.file;

Object gotImportFile(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Expr filename;
  if (!rest(t2, "tree.expr", &filename)) {
    t2.failparse("Couldn't parse file name expression");
  }
  if (!t2.accept(")"))
    t2.failparse("Expected closing paren");
  filename = foldex(filename);
  auto se = fastcast!(StringExpr) (filename);
  if (!se)
    text.failparse("Expected string expr, got ", (cast(Object) filename).classinfo.name);
  auto data = read(se.str);
  auto res = new DataExpr;
  res.data = cast(ubyte[]) data;
  text = t2;
  return fastcast!(Object) (mkFullSlice(res));
}
mixin DefaultParser!(gotImportFile, "tree.expr.import_file", "24065", "import(");
