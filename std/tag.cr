module std.tag;

interface Tag {
  Tag offers(string name);
  string ident();
}

class DefaultTag : Tag {
  string id;
  void init(string s) id = s;
  Tag offers(string s) { return [Tag:null, Tag:this][eval s == id]; }
  string ident() { return id; }
}

interface ITaggedObject : Tag {
  void annotate(Tag t);
}

class Parented : DefaultTag {
  ITaggedObject parent;
  void init() super.init "Parented";
}

class TaggedObject : ITaggedObject, Tag {
  Tag[] extensions;
  string ident() { writeln "Can't call base method for TaggedObject:ident()!"; _interrupt 3; }
  Tag offers(string name) {
    for Tag tag <- extensions {
      if (tag.offers name) return tag;
    }
    return null;
  }
  void annotate(Tag t) {
    auto name = t.ident();
    if auto par = Parented:t.offers "Parented" {
      par.parent = this;
    }
    for int i <- 0..extensions.length
      if (extensions[i].offers name) {
        extensions[i] = t;
        return;
      }
    extensions ~= t;
  }
}

template offersNamed(T) <<EOT
  T offersNamed(Object obj, string name) {
    if !name.length name = T.name;
    if auto t = Tag: obj
      return T: t.offers name;
    return null;
  }
EOT

template offers(T) <<EOT
  T offers(Object obj) {
    return offersNamed!T(obj, string:(null, null));
  }
EOT
