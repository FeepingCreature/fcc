module ast.platform;

import ast.base, parseBase, ast.fun, ast.namespace, ast.pointer;

import ast.modules;
Object gotPlatform(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string platname;
  if (!t2.gotIdentifier(platname) || !t2.accept(")"))
    t2.failparse("Invalid platform directive. ");
  auto src = t2.getHeredoc();
  auto mod = current_module();
  if (platname~"-" == platform_prefix || platname == "default" && !platform_prefix) {
    Tree tr;
    if (!src.many(
        !!rest(src, "tree.toplevel", &tr),
        {
          if (auto n = fastcast!(Named) (tr))
            if (!addsSelf(tr))
              mod.add(n);
          mod.entries ~= tr;
        }
      ))
      src.failparse("Failed to parse platform body. ");
    src.eatComments();
    if (src.mystripl().length) {
      src.failparse("Unknown statement. ");
    }
  }
  text = t2;
  return Single!(NoOp);
}
mixin DefaultParser!(gotPlatform, "tree.toplevel.platform", null, "platform(");
