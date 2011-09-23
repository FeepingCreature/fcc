module ast.modules_parse;

import parseBase, ast.base, ast.parse, ast.modules;

import tools.threads, tools.threadpool, tools.compat: read, castLike, exists, sub;
import ast.structure, ast.namespace;

Object gotImport(ref string text, ParseCb cont, ParseCb rest) {
  string m;
  auto t2 = text;
  bool pub;
  if (t2.accept("public")) pub = true;
  if (!t2.accept("import")) return null;
  text = t2;
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
    if (pub)
      mod.public_imports ~= lookupMod(str);
    else mod.imports ~= lookupMod(str);
  return Single!(NoOp);
}
mixin DefaultParser!(gotImport, "tree.import");

Object gotModule(ref string text, ParseCb cont, ParseCb restart) {
  auto t2 = text;
  Structure st;
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
  Object obj;
  if (t2.many(
      !!restart(t2, "tree.toplevel", &obj),
      {
        if (auto n = fastcast!(Named) (obj))
          if (!addsSelf(obj))
            mod.add(n);
        if (auto tr = fastcast!(Tree) (obj))
          mod.entries ~= tr;
      }
    )
  ) {
    eatComments(t2);
    text = t2;
    if (text.strip().length)
      text.failparse("Unknown statement");
    // logln("do later parsing for ", mod.name);
    doLaterParsing();
    // logln("done");
    mod.parsingDone = true;
    return mod;
  } else t2.failparse("Failed to parse module");
}
mixin DefaultParser!(gotModule, "tree.module", null, "module");

Object gotRename(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Named n;
  string id2;
  if (!rest(t2, "tree.expr.named", &n) && !rest(t2, "type.named", &n)
    ||!t2.gotIdentifier(id2)) {
    t2.failparse("Couldn't get parameter for rename");
  }
  auto ns = namespace();
  ns.rebuildCache();
  auto id1 = n.getIdentifier(), p = id1 in ns.field_cache;
  if (!p) {
    t2.failparse("Cannot rename non-locally, use expression alias instead (", ns.field_cache, ")");
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

import parseBase, tools.log;
Object gotNamed(ref string text, ParseCb cont, ParseCb rest) {
  string name; string t2 = text;
  Namespace ns = namespace();
  bool gotDot;
  if (t2.accept(".")) { gotDot = true; ns = ns.get!(Module); } // module-scope lookup
  if (t2.gotIdentifier(name, true)) {
    retry:
    if (auto res = ns.lookup(name)) {
      if (auto ty = fastcast!(IType) (res))
        if (!fastcast!(ExprLikeThingy)(resolveType(ty)))
          return null; // Positively NOT an expr, and not a thingy either.
      if (gotDot) if (!text.accept("."))
        text.failparse("No dot?! ");
      if (!text.accept(name))
        text.failparse("WTF ", name);
      
      if (auto ex = fastcast!(Expr) (res))
        return fastcast!(Object) (forcedConvert(ex));
      return res;
      
    } else {
      // logln("No ", name, " in ", ns);
    }
    int dotpos = name.rfind("."), dashpos = name.rfind("-");
    if (dotpos != -1 && dashpos != -1)
      if (dotpos > dashpos) goto checkDot;
      else goto checkDash;
    
    checkDash:
    if (t2.eatDash(name)) goto retry;
    
    checkDot:
    if (dotpos != -1) {
      name = name[0 .. dotpos]; // chop up what _may_ be members!
      goto retry;
    }
    
    t2.setError("unknown identifier: '", name, "'");
  }
  return null;
}
