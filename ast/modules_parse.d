module ast.modules_parse;

import parseBase, ast.base, ast.parse, ast.modules;

import tools.threads, tools.threadpool, tools.base: read, castLike, exists, sub;
import ast.structure, ast.namespace;

version(Windows) string myRealpath(string s) { return s; }
else {
  extern(C) char* realpath(char* fn, char* wtf = null);
  string myRealpath(string s) { return toString(realpath(toStringz(s))); }
}

Object gotImport(bool ReturnNamed)(ref string text, ParseCb cont, ParseCb rest) {
  bool pub, stat;
  auto original_text = text;
  {
    auto t2 = text;
    if (t2.accept("public"[])) pub = true;
    else if (t2.accept("static"[])) stat = true;
    if (!t2.accept("import"[])) return null;
    text = t2;
  }
  auto cap = namespace().get!(Importer);
  string[] newImports;
  {
    string[][] importstack; importstack ~= null;
    auto t2 = text;
    string m;
    // State machines are most effectively expressed as a goto-based structure.
    // I'm .. I'm sorry, everybody.
    
    string t3;
  expect_identifier:
    t3 = t2;
    if (!t3.gotIdentifier(m, true)) {
      // std.foo(bar,) or std.foo(,bar)
      if (t3.accept(","[]) || t3.accept(")"[]))
        m = "";
      else
        t2.failparse("Import identifier expected"[]);
      t3 = t2;
    }
    if (auto pre = m.endsWith("."[])) { // nuh
      m = pre;
      t3 = t2;
      if (!t3.accept(m))
        fail;
    }
    t2 = t3;
    importstack[$-1] ~= m;
  
  expect_separator:
    if (t2.accept(","[]))
      goto expect_identifier;
    t3 = t2;
    if (t3.accept("."[]) && t3.accept("("[])) {
      t2 = t3;
      importstack ~= null;
      goto expect_identifier;
    }
    t3 = t2;
    if (t3.accept("("[])) {
      t2.failparse("Expected dot before opening parenthesis for group import"[]);
    }
    if (t2.accept(")"[])) {
      auto block = importstack[$-1];
      importstack = importstack[0..$-1];
      if (!importstack.length) t2.failparse("Too many closing parentheses"[]);
      if (!importstack[$-1].length) t2.failparse("Invalid import statement structure"[]);
      auto prefix = importstack[$-1][$-1];
      importstack[$-1] = importstack[$-1][0..$-1];
      foreach (ref entry; block) {
        if (entry.length) entry = prefix ~ "." ~ entry;
        else entry = prefix;
      }
      importstack[$-1] ~= block;
      goto expect_separator;
    }
    if (importstack.length != 1)
      t2.failparse("Not enough closing parentheses"[]);
    if (!t2.accept(";"[]))
      t2.failparse("Terminating semicolon expected"[]);
    if (!importstack[$-1].length)
      t2.failparse("Nothing is being imported"[]);
    
    newImports = importstack[$-1];
    text = t2;
  }
  void process(Importer cap, ImportType type, Module newmod) {
    auto test = cap;
    while (test) {
      Namespace[] list = test.getImports();
      foreach (entry; list) if (auto mod = fastcast!(Module) (entry)) {
        if (mod.name == newmod.name) text.failparse("Duplicate import"[]);
      }
      bool succeed;
      if (auto ns = fastcast!(Namespace) (test)) if (ns.sup) { test = ns.sup.get!(Importer); succeed = true; }
      if (!succeed) test = null;
    }
    (*cap.getImportsPtr(type)) ~= newmod;
  }
  foreach (str; newImports) {
    auto newmod = lookupMod(str);
    if (!newmod)
      original_text.failparse("Could not find module "[], str);
    if (pub) process(cap, ImportType.Public, newmod);
    else if (stat) process(cap, ImportType.Static, newmod);
    else process(cap, ImportType.Regular, newmod);
  }
  static if (ReturnNamed) {
    return new NamedNull;
  } else {
    return Single!(NoOp);
  }
}
mixin DefaultParser!(gotImport!(false), "tree.import");
mixin DefaultParser!(gotImport!(false), "tree.semicol_stmt.import", "102");
mixin DefaultParser!(gotImport!(true), "struct_member.import");

Object gotModule(ref string text, ParseCb cont, ParseCb restart) {
  auto t2 = text;
  Structure st;
  Module mod;
  auto backup = namespace.ptr();
  scope(exit) namespace.set(backup);
  string modname;
  if ((!(t2.accept("auto") && (modname = "auto", true)) && !t2.gotIdentifier(modname, true)) || !t2.accept(";"[]))
    t2.failparse("Failed to parse module header, 'module' expected! "[]);
  
  {
    auto filemod = lookupPos(t2)._2.endsWith(".nt"[]).replace("/"[], "."[]);
    if (modname == "auto"[]) {
      modname = filemod;
    }
    if (filemod && !filemod.endsWith(modname)) {
      text.failparse("The module name '"[], modname, "' does not match the filename"[]);
    }
  }
  
  New(mod, modname, myRealpath(lookupPos(t2)._2));
  
  modules_wip[modname] = mod;
  scope(exit) modules_wip.remove(modname);
  
  namespace.set(mod);
  auto backup_mod = current_module();
  scope(exit) current_module.set(backup_mod);
  current_module.set(mod);
  
  
  if (mod.name == "sys"[]) {
    sysmod = mod; // so that internal lookups work
  }
  Object obj;
  if (t2.many(
      !!restart(t2, "tree.toplevel"[], &obj),
      {
        if (auto n = fastcast!(Named) (obj))
          if (!addsSelf(obj))
            mod.add(n);
        if (auto tr = fastcast!(Tree) (obj))
          mod.addEntry(tr);
      }
    )
  ) {
    eatComments(t2);
    text = t2;
    if (text.strip().length)
      text.failparse("Unknown statement"[]);
    // logln("do later parsing for "[], mod.name);
    // logln("done"[]);
    mod.parsingDone = true;
    return mod;
  } else t2.failparse("Failed to parse module"[]);
}
mixin DefaultParser!(gotModule, "tree.module"[], null, "module"[]);

Object gotRename(ref string text, ParseCb cont, ParseCb rest) {
  auto t2 = text;
  Named n;
  string id2;
  if (!rest(t2, "tree.expr.named"[], &n) && !rest(t2, "type.named"[], &n)
    ||!t2.gotIdentifier(id2)) {
    t2.failparse("Couldn't get parameter for rename"[]);
  }
  auto ns = namespace();
  ns.rebuildCache();
  auto id1 = n.getIdentifier(), p = id1 in ns.field_cache;
  if (!p) {
    t2.failparse("Cannot rename non-locally, use expression alias instead ("[], ns.field_cache, ")"[]);
  }
  if (!t2.accept(";"[]))
    t2.failparse("Expected trailing semicolon in rename! "[]);
  auto pd = *p;
  foreach (ref entry; ns.field) {
    if (entry._0 == id1) { entry._0 = id2; entry._1 = pd; break; }
  }
  ns.rebuildCache();
  text = t2;
  return Single!(NoOp);
}
mixin DefaultParser!(gotRename, "tree.toplevel.a_rename"[], null, "RenameIdentifier"[]); // sort first because is cheap to exclude

import parseBase, tools.log;
Object gotNamed(ref string text, ParseCb cont, ParseCb rest) {
  string name; string t2 = text;
  Namespace ns = namespace();
  bool gotDot;
  if (t2.accept(".")) { gotDot = true; ns = ns.get!(Module); } // module-scope lookup
  if (t2.gotIdentifier(name, true)) {
    int dot_end;
    while (dot_end < name.length) {
      // for each dot-separated component .. 
      int dotpos = name[dot_end..$].find(".");
      string ident;
      if (dotpos == -1) {
        ident = name;
        dot_end = name.length;
      } else {
        ident = name[0..dot_end + dotpos];
        dot_end += dotpos + 1;
      }
      retry:
      // hack: get t2 into its expected state
      t2 = text;
      if (gotDot) t2.accept(".");
      if (!t2.accept(ident)) t2.failparse("wat :(");
      
      if (auto res = ns.lookup(ident)) {
        if (auto ty = fastcast!(IType) (res)) {
          if (t2.accept(":"[])) return null; // HACK: oops, was a cast
          if (!fastcast!(ExprLikeThingy)(resolveType(ty)))
            return null; // Positively NOT an expr, and not a thingy either.
        }
        if (gotDot) if (!text.accept("."[]))
          text.failparse("No dot?! "[]);
        if (!text.accept(ident))
          text.failparse("WTF "[], ident);
        
        if (auto ex = fastcast!(Expr) (res))
          return fastcast!(Object) (forcedConvert(ex));
        return res;
      }
      // only do this for the full identifier, but not if it's a compound (too many false hits)
      if (ident.length == name.length && ident.find(".") == -1) {
        unknownId(ident, t2);
      }
      
      auto pos_dot = ident.rfind("."), pos_dash = ident.rfind("-");
      // if we have any dashes in our current ident's rightmost component ..
      if (pos_dash != -1 && (pos_dot == -1 || pos_dot < pos_dash) && t2.eatDash(ident))
        goto retry;
    }
  }
  return null;
}
