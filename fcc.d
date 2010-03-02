module fcc; // feep's crazed compiler

import tools.base, tools.log, tools.compat;

import fraclist;

extern(C) {
  int mkstemp(char* tmpl);
  int close(int fd);
}

string tmpnam(string base = "fcc") {
  string name = base ~ "XXXXXX";
  auto p = toStringz(name);
  auto fd = mkstemp(p);
  assert(fd != -1);
  close(fd);
  return toString(p);
}

bool isAlpha(dchar d) {
  // TODO expand
  return d >= 'A' && d <= 'Z' || d >= 'a' && d <= 'z';
}

bool isAlphanum(dchar d) {
  return isAlpha(d) || d >= '0' && d <= '9';
}

template Placeholder(T, string Name) {
  mixin(`Ret!(T) `~Name~`(Params!(T) p) { assert(false, Format(this, " doesn't implement `~Name~`()! ")); }`);
}

struct EntParIter {
  Entity start;
  int opApply(int delegate(Entity) dg) {
    auto ent = start;
    while (ent) {
      if (auto res = dg(ent)) return res;
      ent = ent.parent;
    }
    return 0;
  }
}

class Entity {
  char* text_start;
  Entity parent;
  Entity setParent(Entity par) {
    assert(!parent); // cannot replant
    parent = par;
    return this;
  }
  mixin Placeholder!(void function(Entity what, Entity newEnt), "replace");
  void overwrite(Entity newEnt) {
    assert(parent);
    parent.replace(this, newEnt.setParent(parent));
  }
  void iterate(void delegate(Entity) dg) { }
  EntParIter par_iter() { return EntParIter(this); }
  string toString() {
    return Format(super.toString(), "(", cast(void*) parent, ")");
  }
}

class FileEntity : Entity {
  string filename;
  FracString text;
}

void delegate(Entity) normPass(C)(C c) {
  return c /apply/ (C c, Entity ent) { // close over c
    alias Params!(C)[0] T;
    if (auto te = cast(T) ent) {
      c(te);
      ent = te;
    }
  };
}

void delegate(Entity)[string] passes;

import tools.ctfe;
// default constructors
string ctDefCon(string vars) {
  bool placeSupCon = true;
  string res = "
  this() { }
  this(typeof(this) n) {";
  while (vars.length) {
    string var = vars.ctSlice(" ").ctStrip();
    // allow ", " separation
    if (var.length && var[$-1] == ',')
      var = var[0 .. $-1];
    if (var == "!nosupcon") {
      placeSupCon = false;
      continue;
    }
    res ~= "this."~var~" = n."~var~"; ";
  }
  res ~= "}";
  if (placeSupCon) {
    res ~= "
  // fuck me I've landed in Lisp Land
  // if super copy constructs, forward to it
  static if (is(typeof(new typeof(super)(Init!(typeof(super))))))
    this(typeof(super) s) { super(s); }
    ";
  }
  return res;
}

class Section : Entity {
  string name;
  FracString text;
  mixin(ctDefCon("name text"));
  mixin Placeholder!(string function(), "generate");
  string toString() {
    return Format(super.toString(), ": \"", text, "\"");
  }
}

class MetaSection : Section {
  FracString[] lines;
  mixin(ctDefCon("!nosupcon lines"));
  this(Section s) {
    super(s);
    lines = text.split("\n");
  }
  string toString() {
    return Format(super.toString(), ": ", lines);
  }
  static void pass(Section s) {
    if (s.name != "meta") return;
    s.overwrite(new MetaSection(s));
  }
  static this() {
    passes["meta-section"] = normPass(&pass);
  }
}

class Root : Entity {
  mixin(ctDefCon("child"));
  this(Entity ent) { child = ent.setParent(this); }
  Entity child;
  void iterate(void delegate(Entity) dg) { dg(child); }
  void replace(Entity a, Entity b) {
    if (child is a) child = b;
  }
}

class SectionFile : FileEntity {
  Section[string] entries;
  void iterate(void delegate(Entity) dg) {
    foreach (key, value; entries) dg(value);
  }
  void replace(Entity what, Entity n) {
    assert(cast(Section) n);
    foreach (key, ref value; entries)
      if (value is what)
        value = cast(Section) n;
  }
  static void pass(FileEntity fe) {
    auto nfe = new SectionFile;
    nfe.filename = fe.filename;
    auto text = nfe.text = fe.text;
    string secname;
    FracString rest;
    if (text.startsWith("%", rest)) {
      secname = cast(string) rest.slice("\n");
      text = text[1+secname.length .. $]; // include newline!
    } else return; // not a sectioned file
    scope(success) fe.overwrite(nfe);
    while (true) {
      auto sec_end = text.find("\n%");
      if (sec_end == -1) {
        auto ns = new Section;
        ns.parent = nfe;
        ns.text = text[1 .. $];
        nfe.entries[ns.name = secname] = ns;
        break;
      }
      auto ns = new Section;
      ns.parent = nfe;
      ns.text = text[1 .. sec_end + 1];
      nfe.entries[ns.name = secname] = ns;
      text = text[sec_end + 1 .. $];
      auto temp = text[1 .. $];
      secname = cast(string) temp.slice("\n");
      text = text[1+secname.length .. $];
    }
  }
  static this() {
    passes["section-file"] = normPass(&pass);
  }
  string toString() {
    return Format(super.toString(), " (", entries, ")");
  }
}

struct DepthFirst {
  Entity root;
  int opApply(int delegate(ref Entity) dg) {
    int recurse(Entity ent) {
      int res;
      ent.iterate((Entity e) {
        if (!res) res = recurse(e);
      });
      if (!res) res = dg(ent);
      return res;
    }
    return recurse(root);
  }
}

void applyPass(Entity ent, string name) {
  auto dg = passes[name];
  foreach (ent; DepthFirst(ent)) {
    // logln("apply ", name, " to ", ent);
    dg(ent);
  }
}

string compile(string file) {
  auto srcname = tmpnam("fcc_src"), objname = tmpnam("fcc_obj");
  scope(exit) {
    unlink(srcname.toStringz());
    // TODO move to linker when actually linkable
    unlink(objname.toStringz());
  }
  auto fe = new FileEntity;
  fe.text = FracString([file.read().castLike("")]);
  fe.filename = file;
  {
    Entity ent = new Root(fe);
    applyPass(ent, "section-file");
    applyPass(ent, "meta-section");
    fe = cast(typeof(fe)) (cast(Root) ent).child;
  }
  logln("Product: ", fe);
  // srcname.write(fe.generate()); // TODO: actually compile  
  return null;
}

void main(string[] args) {
  auto exec = args.take();
  string[] objects;
  string output;
  auto ar = args;
  string[] largs;
  while (ar.length) {
    auto arg = ar.take();
    if (arg == "-o") {
      output = ar.take();
      continue;
    }
    if (arg.startsWith("-l")) {
      largs ~= arg;
      continue;
    }
    if (auto base = arg.endsWith(".cr")) {
      if (!output) output = arg[0 .. $-3];
      objects ~= arg.compile();
      continue;
    }
    return logln("Invalid argument: ", arg);
  }
  if (!output) output = "exec";
  logln("Skip linking");
  // objects.link(output, largs);
}
