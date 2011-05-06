module std.tag;

interface Tag {
  Tag implements(string name);
  string ident();
}

class DefaultTag : Tag {
  string id;
  void init(string s) id = s;
  Tag implements(string s) { return [Tag:null, Tag:this][eval s == id]; }
  string ident() { return id; }
}

interface ITaggedObject {
  Tag hasTag(string name);
  void annotate(Tag t);
}

class Parented : DefaultTag {
  ITaggedObject parent;
  void init() super.init "Parented";
}

class TaggedObject : ITaggedObject {
  Tag[] extensions;
  Tag hasTag(string name) {
    for Tag tag <- extensions {
      if (tag.implements name) return tag;
    }
    return null;
  }
  void annotate(Tag t) {
    auto name = t.ident();
    if auto par = Parented:t.implements "Parented" {
      par.parent = this;
    }
    for int i <- 0..extensions.length
      if (extensions[i].implements name) {
        extensions[i] = t;
        return;
      }
    extensions ~= t;
  }
}

template hasTag(T) <<EOT
  T hasTag(ITaggedObject obj) {
    return T: obj.hasTag(T.name);
  }
EOT

template offers(T) <<EOT
  T offers(Object obj) {
    if auto ito = ITaggedObject: obj
      return T: ito.hasTag(T.name);
    if auto t = Tag: obj
      return T: t.implements T.name;
    return null;
  }
EOT
