module alsatest;

import std.sort, std.math, std.sound;

void cfgNote(Note res, float freq, float len) {
  res.freq = freq;
  using res {
    maxVolume = 0.2;
    sustain = 0.1;
    decayStart = len * 0.05;
    sustainStart = len * 0.3;
    releaseStart = len * 0.7;
    end = len;
  }
}

void main(string[] args) {
  (string exec, args) = args[(0, 1..$)];
  Sound snd;
  if (args.length && args[0] == "-oss")
    snd = new OSSSound("/dev/dsp");
  else
    snd = new AlsaSound("default");
  
  snd.open();
  float delegate(float) dg;
  int length = 1024;
  int fadeout = 4096;
  float[12] scale;
  for int i <- 0..12
    scale[i] = pow(pow(2, 1/12f), i);
  
  (Note, float)[] notelist;
  void addNoteAt(float start, float freq, float length) {
    // writeln "addNoteAt($start, $freq, $length)";
    (Note, float)[auto~] res;
    for int i <- 0..notelist.length res ~= notelist[i];
    Note n = new KarplusStrongNote;
    cfgNote(n, freq, length);
    res ~= (n, start);
    notelist = res[];
  }
  void addNoteAtRef(float* pp, float freq, float len) {
    alias pos = *pp;
    addNoteAt(pos, freq, len);
    pos += len;
  }
  void clearList(float pos) {
    (Note, float)[auto~] res;
    for int i <- 0..notelist.length {
      alias n = notelist[i];
      if pos < (n[1] + n[0].end) res ~= n;
    }
    notelist = res[];
  }
  void sortList() { qsort!"eval (%a[1]) < (%b[1])" notelist; }
  void addTrack(string notes) {
    float baseFreq = 220;
    float len = 0.3705;
    int octaves; // int so it doesn't get fucked up by repeated mul/div
    float lenf = 1;
    float offs = 0;
    alias state = (baseFreq, len, lenf, offs);
    type-of state[] stack;
    char lastChar;
    while notes.length {
      (char cur, notes) = notes[(0, 1..$)];
      if cur == "."[0] { lenf = 1.5; }
      else {
        auto l = len * lenf;
        void handleChar(char ch) {
               if ch == "c" addNoteAtRef(&offs, baseFreq * scale[0], l);
          else if ch == "d" addNoteAtRef(&offs, baseFreq * scale[2], l);
          else if ch == "e" addNoteAtRef(&offs, baseFreq * scale[4], l);
          else if ch == "f" addNoteAtRef(&offs, baseFreq * scale[5], l);
          else if ch == "g" addNoteAtRef(&offs, baseFreq * scale[7], l);
          else if ch == "a" addNoteAtRef(&offs, baseFreq * scale[9], l);
          else if ch == "b" addNoteAtRef(&offs, baseFreq * scale[10], l);
          else if ch == "h" addNoteAtRef(&offs, baseFreq * scale[11], l);
          else if ch == "_" offs += l;
          else if ch == ">" octaves ++;
          else if ch == "<" octaves --;
          else if ch == "+" len *= 2;
          else if ch == "-" len /= 2;
          else if ch == "[" stack ~= (baseFreq, len, lenf, offs);
          else if ch == "]" stack = stack[0 .. $-1];
          else if ch == "," (baseFreq, len, lenf, offs) = stack[$-1];
        }
        if (cur >= "0" && cur <= "9") {
          int num = cur - "0";
          while notes.length && notes[0] >= "0" && notes[0] <= "9" {
            num = num * 10 + (notes[0] - "0");
            notes = notes[1 .. $];
          }
          for 0..(num - 1)
            handleChar lastChar;
        } else handleChar cur;
        lastChar = cur;
        lenf = 1;
        baseFreq = 220 * pow(2, octaves);
      }
    }
  }
  // addTrack "<a>e<h>ec-de+dg-aeh>c<h->c<h+agegde+.c<-h+ a>e<h>ec-de+dg-aeh>c<h->c<h+ag++a";
  // addTrack "<+fgaefgaefgaefg+a";
  string str = "-efef+ga-efef+ga-cdcd+ef-cdcd+fe", st2;
  for 0..8 st2 ~= str;
  st2 ~= "-c8d8<b8f4e4>c8d8<b8++fg--b8>c8<a8>d4c4<b8>c8<a8>d4c4<b14__+>";
  for 0..2 st2 ~= str;
  st2 ~= "-_>[f16,c16]  [d16,<a16>][f16,c16]  [d14__,<a14__>]<+";
  st2 ~= "- <[f16,>c16<][d16,a16]  [f16,>c16<][d15,a15]+>";
  for 0..2 st2 ~= str;
  st2 ~= "-<b8>c8<a8>d4c4<b8>c8<a8>d4c4<b14__+>";
  addTrack st2;
  sortList();
  writeln "added $(notelist.length) notes";
  int lastDoneAt;
  dg = delegate float(float f) {
    float res = 0f;
    bool done;
    int i;
    while !done && i < notelist.length {
      alias n = notelist[i];
      if (f >= n[1]) {
        if f < n[1] + n[0].end res += n[0].calcValue (f - n[1]);
      } else {
        done = true;
        auto doneAt = i;
        if (doneAt != lastDoneAt) clearList f;
        lastDoneAt = doneAt;
      }
      i++;
    }
    return res;
  };
  int base;
  while true {
    snd.dump(delegate Sample(int i) {
      auto res = Sample:short:int:(dg((base + i) / 48000f) * 32767f);
      return res;
    }, length, 1f);
    base += length;
  }
  snd.close();
}
