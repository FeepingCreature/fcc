module ast.modules_parse;

import parseBase, ast.base, ast.parse, ast.modules;

import tools.threads, tools.threadpool, tools.compat: read, castLike, exists, sub;
import ast.structure, ast.namespace;

Object gotImport(ref string text, ParseCb cont, ParseCb rest) {
  string m;
  // import a, b, c;
  auto mod = current_module();
  string[] newImports;
  if (!(
    text.bjoin(text.gotIdentifier(m, true), text.accept(","),
    { newImports ~= m; },
    true) &&
    text.accept(";")
  )) text.failparse("Unexpected text while parsing import statement");
  foreach (str; newImports)
    mod.imports ~= lookupMod(str);
  return Single!(NoOp);
}
mixin DefaultParser!(gotImport, "tree.import", null, "import");

Object gotModule(ref string text, ParseCb cont, ParseCb restart) {
  auto t2 = text;
  Structure st;
  Tree tr;
  Module mod;
  auto backup = namespace.ptr();
  scope(exit) namespace.set(backup);
  string modname;
  if (!t2.gotIdentifier(modname, true) || !t2.accept(";"))
    t2.failparse("Failed to parse module header, 'module' expected! ");
  
  New(mod, modname);
  namespace.set(mod);
  auto backup_mod = current_module();
  scope(exit) current_module.set(backup_mod);
  current_module.set(mod);
  
  
  if (mod.name == "sys") {
    sysmod = mod; // so that internal lookups work
  }
  if (t2.many(
      !!restart(t2, "tree.toplevel", &tr),
      {
        if (auto n = fastcast!(Named)~ tr)
          if (!addsSelf(tr))
            mod.add(n);
        mod.entries ~= tr;
      }
    )
  ) {
    eatComments(t2);
    text = t2;
    if (text.strip().length)
      text.failparse("Unknown statement");
    mod.parsingDone = true;
    return mod;
  } else t2.failparse("Failed to parse module");
}
mixin DefaultParser!(gotModule, "tree.module", null, "module");

Object gotRename(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Named n;
  string id2;
  if (!rest(t2, "tree.expr.named", &n)
    ||!t2.gotIdentifier(id2)) {
    t2.failparse("Couldn't get parameter for rename");
  }
  auto ns = namespace();
  auto id1 = n.getIdentifier(), p = id1 in ns.field_cache;
  if (!p) {
    t2.failparse("Cannot rename non-locally, use expression alias instead");
  }
  if (!t2.accept(";"))
    t2.failparse("Expected trailing semicolon in rename! ");
  auto pd = *p;
  ns.field_cache.remove(id1);
  ns.field_cache[id2] = pd;
  ns.rebuildField();
  text = t2;
  return Single!(NoOp);
}
mixin DefaultParser!(gotRename, "tree.toplevel.rename", null, "RenameIdentifier");
