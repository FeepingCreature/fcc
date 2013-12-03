// int[] foo; for x in foo maximize x;
// int[] foo; foo #.maximize λ(int x) -> x;
module ast.forex;

import parseBase, ast.base;
import ast.casting, ast.namespace, ast.scopes, ast.returns;
import ast.modules, ast.iterator;
import ast.fun, ast.nestfun;
Object gotForEx(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string label;
  if (!t2.gotIdentifier(label)) t2.failparse("identifier expected");
  if (!t2.accept("in")) t2.failparse("'in' expected after identifier");
  
  Expr arg1;
  
  if (!rest(t2, "tree.expr _tree.expr.bin.math", &arg1))
    t2.failparse("Expected start iterator for 'for' expression");
  
  while (true) {
    auto t3 = t2;
    
    string fun_name;
    if (!t2.gotIdentifier(fun_name))
      break;
    if (fun_name == "as") { // rename
      if (!t2.gotIdentifier(label)) t2.failparse("'as' expected new identifier");
      else continue;
    }
    
    // belongs inside the loop because we'll repeat it for the next loop pass
    // using the new arg1
    auto ex = arg1;
    bool isIterator(IType it) { return !!fastcast!(Iterator)(resolveType(it)); }
    if (!gotImplicitCast(arg1, Single!(HintType!(Iterator)), &isIterator))
      t2.failparse("Expected iterator type for 'for' expression, not ", ex.valueType());
    
    auto itr = fastcast!(Iterator)(resolveType(arg1.valueType()));
    IType argtype = itr.elemType();
    // logln("at ", t2.nextText(), ": argtype = ", argtype);
    
    if (fun_name == "eval") { // #.eval
      arg1 = fastalloc!(EvalIterator!(Iterator))(arg1, itr);
      continue;
    }
    
    auto sc = namespace().get!(Scope);
    
    // construct the surrounding lambda for the expr
    auto nf = fastalloc!(NestedFunction)(sc), mod = fastcast!(Module) (current_module());
    
    New(nf.type);
    nf.sup = mod;
    nf.type.params ~= Argument(argtype, label);
    
    static int forex_lambda_id;
    synchronized
      nf.name = Format("forex_lambda_"[], forex_lambda_id++);
    
    Expr arg2;
    {
      auto backup = namespace();
      scope(exit) namespace.set(backup);
      
      namespace.set(nf);
      nf.fixup;
      
      auto sc2 = new Scope;
      namespace.set(sc2);
      
      Expr return_ex;
      if (!rest(t2, "tree.expr", &return_ex))
        t3.failparse("'for' expr lambda expression failed to match");
      
      nf.type.ret = return_ex.valueType();
      
      sc2.addStatement(fastalloc!(ReturnStmt)(return_ex));
      nf.addStatement(sc2);
    }
    mod.addEntry(fastcast!(Tree)(nf));
    namespace().get!(Function).dependents ~= nf;
    
    arg2 = fastalloc!(NestFunRefExpr)(nf);
    
    auto callme = sc.lookup(fun_name, false);
    if (!callme) t3.failparse("unknown identifier '", fun_name, "'");
    
    try {
      auto call = iparse!(Expr, "forex call", "tree.expr")
                         (`fun (arg1, arg2)`,
                          "fun", callme, "arg1", arg1, "arg2", arg2);
      
      arg1 = call;
    } catch (Exception ex) {
      t3.failparse("while trying to generate for expression: ", ex);
    }
  }
  
  text = t2;
  return fastcast!(Object)(arg1);
}
mixin DefaultParser!(gotForEx, "tree.expr.forex", "24048", "for");
