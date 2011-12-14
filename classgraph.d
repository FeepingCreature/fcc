module classgraph;

import tools.base: startsWith, or, rslice, Format, stuple, Stuple;
import tools.compat: replace, write;

// class graph gen
import std.moduleinit, tools.log;

void genGraph(string filename, bool drawModules = true, bool drawClasses = true, bool nested = true) {
  nested &= drawClasses && drawModules;
  
  ClassInfo[string] classfield;
  string[][string] imports;
  bool[string] modules;
  bool ignore(string s) {
    return !!s.startsWith("std."[] /or/ "object"[] /or/ "TypeInfo"[] /or/ "gcx"[]);
  }
  foreach (mod; ModuleInfo.modules()) {
    modules[mod.name] = true;
    foreach (mod2; mod.importedModules) {
      if (!mod.name.ignore() && !mod2.name.ignore()) {
        modules[mod2.name] = true;
        imports[mod.name] ~= mod2.name;
      }
    }
    foreach (cl; mod.localClasses) {
      if (!ignore(cl.name))
        classfield[cl.name] = cl;
      foreach (intf; cl.interfaces)
        if (!ignore(intf.classinfo.name))
          classfield[intf.classinfo.name] = intf.classinfo;
    }
  }
  auto classes = classfield.values;
  
  string res = "Digraph G {
    rankdir=LR; compound=true;
    "/*concentrate=true; disabled because it crashes dot*/"
    remincross=true;\n";
  scope(success) filename.write(res);
  scope(success) res ~= "}\n";
  
  string[][string] mod2class;
  string[string] name2label;
  
  string filterName(string n) {
    // ugly band-aid to filter invalid characters
    return n.replace(".", "_").replace("!", "_").replace("(", "_").replace(")", "_");
  }
  foreach (cl; classes) {
    auto classname = cl.name, mod = classname.rslice(".");
    mod2class[mod] ~= filterName(cl.name);
    name2label[filterName(cl.name)] = classname;
  }
  bool[string] import_relevant;
  foreach (key, value; imports) {
    import_relevant[key] = true;
    foreach (p; value)
      import_relevant[p] = true;
  }
  string marker(string mod) {
    return "marker_"~mod.replace(".", "_");
  }
  string cluster(string mod) {
    return "cluster_"~mod.replace(".", "_");
  }
  auto nestClasses = drawClasses && nested;
  if (drawModules) {
    if (nestClasses) {
      foreach (key, value; modules) {
        if (!key) continue;
        res ~= "subgraph " ~ key.cluster() ~ " {\n";
        res ~= "label=\"" ~ key ~ "\"; \n";
        if (key in import_relevant)
          res ~= key.marker() ~ " [style=invis, width=0, height=0, fontsize=0]; \n";
        if (auto p = key in mod2class)
          foreach (cl; *p) {
            res ~= cl ~ " [label=\"" ~ name2label[cl]~"\", shape=box]; \n";
          }
        res ~= "}\n";
      }
    } else {
      foreach (key, value; modules) {
        if (!key) continue;
        if (!(key in import_relevant)) continue;
        res ~= key.marker() ~ " [label=\"" ~ key ~ "\"]; \n";
      }
    }
    bool[string] linkAdded;
    foreach (key, value; modules) {
      if (auto p = key in imports)
        foreach (mod2; *p) {
          if (key.marker()~"!"~mod2.marker() in linkAdded) continue;
          else linkAdded[key.marker()~"!"~mod2.marker()] = true;
          res ~= key.marker() ~ " -> " ~ mod2.marker()
            ~ " [color=blue,penwidth=1.9"/*constraint=false,*/;
          if (nestClasses)
            res ~= ", style=dotted, ltail=" ~ key.cluster() ~ ", lhead=" ~ mod2.cluster();
          res ~= "];\n";
        }
    }
  }
  if (drawClasses) {
    if (!nestClasses) {
      foreach (key, value; modules) {
        if (!key) continue;
        if (!(key in import_relevant)) continue;
        if (auto p = key in mod2class) {
          foreach (cl; *p)
            res ~= cl ~ " [label=\"" ~ name2label[cl]~"\"]; \n";
        }
      }
    }
    foreach (cl; classes) {
      auto name = cl.name;
      if (cl.base && !cl.base.name.ignore())
        res ~= filterName(name) ~ " -> " ~ filterName(cl.base.name) ~ " [color=red,penwidth=1.8]; \n";
      foreach (i2; cl.interfaces) {
        if (!i2.classinfo.name.ignore())
          res ~= filterName(name) ~ " -> "~filterName(i2.classinfo.name)~" [color=red,style=dashed,penwidth=1.8]; \n";
      }
    }
  }
}
