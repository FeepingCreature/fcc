module fastalloc;

import tools.base, tools.log;

template blockcache(T) {
  void[] memory;
  int class_size;
  int getSize() {
    if (!class_size) {
      class_size = T.classinfo.init.length;
    }
    return class_size;
  }
  T allocate() {
    auto sz = getSize();
    if (memory.length < sz) memory = new void[sz*16];
    auto data = memory[0..sz];
    memory = memory[sz .. $];
    data[] = T.classinfo.init;
    return cast(T) cast(void*) data.ptr;
  }
}

template fastalloc(T) {
  T fastalloc(U...)(U u) {
    auto res = blockcache!(T).allocate();
    // logln("construct ", T.stringof, "(", blockcache!(T).getSize(), ") with ", u);
    res.construct(u);
    return res;
  }
}
