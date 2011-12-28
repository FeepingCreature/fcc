module ast.platform;

import ast.base, parseBase, ast.fun, ast.namespace, ast.pointer, ast.stringparse;

import ast.modules;
Object gotPlatform(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  string platname;
  bool neg, wild;
  if (t2.accept("!")) neg = true;
  if (!t2.gotIdentifier(platname))
    t2.failparse("Invalid platform identifier");
  if (t2.accept("*")) wild = true;
  if (!t2.accept(")"))
    t2.failparse("expected closing paren");
  t2.noMoreHeredoc();
  auto src = t2.coarseLexScope(true, false);
  auto mod = current_module();
  bool match = platname~"-" == platform_prefix || platname == "default" && !platform_prefix;
  if (wild) match |= !!platform_prefix.startsWith(platname);
  if (neg) match = !match;
  if (match) {
    Object obj;
    if (!src.many(
        !!rest(src, "tree.toplevel", &obj),
        {
          if (auto n = fastcast!(Named) (obj))
            if (!addsSelf(obj))
              mod.add(n);
          if (auto tr = fastcast!(Tree) (obj)) mod.entries ~= tr;
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
