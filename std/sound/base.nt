module std.sound.base;

alias Sample = short;

class Sound {
  void open() { writeln "unoverridden open()! "; _interrupt 3; }
  void close() { writeln "unoverridden close()! ";  _interrupt 3; }
  Sample[] copydump;
  void writeCopydump(int len) { writeln "unoverridden writeCopydump()! ";  _interrupt 3; }
  void dump(Sample delegate(int) dg, int newlen, float mult) {
    if (copydump.length < newlen) copydump = new Sample[newlen];
    for int i <- 0..newlen {
      auto value = Sample:short:int:(dg(i) * mult);
      copydump[i] = value;
    }
    writeCopydump(newlen);
  }
  void dump(Sample[] data, float mult) {
    if (copydump.length < data.length) copydump = new Sample[data.length];
    for int i <- 0..data.length
      copydump[i] = Sample:short:int:(data[i]*mult);
    writeCopydump(data.length);
  }
}
