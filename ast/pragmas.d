module ast.pragmas;

import ast.base, parseBase;

Object delegate(Expr)[string] pragmas;

Object gotPragma(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  if (!t2.accept("("))
    t2.failparse("Expected opening paren! ");
  string pragname;
  if (!t2.gotIdentifier(pragname))
    t2.failparse("Identifier expected. ");
  Expr param;
  if (t2.accept(","))
    if (!rest(t2, "tree.expr", &param))
      t2.failparse("Expected pragma parameter. ");
  if (!t2.accept(")")) t2.failparse("Expected closing paren! ");
  if (!t2.accept(";")) t2.failparse("Expected terminating semicolon! ");
  
  auto dg = pragname in pragmas;
  if (!dg) text.failparse("No such pragma! ");
  scope(success) text = t2;
  try return (*dg)(param);
  catch (Exception ex) text.failparse("In pragma ", pragname, ": ", ex);
}

mixin DefaultParser!(gotPragma, "tree.toplevel.pragma", null, "pragma");
