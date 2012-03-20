module quickformat;

import tools.threads: TLS;
import tools.base: New, max;
import casts;

TLS!(string) _qbuffer;
TLS!(int) _offs;
static this() { New(_qbuffer); New(_offs); }

void qformat_append(T...)(T t) {
  string qbuffer = cast(string) _qbuffer();
  int offs = cast(int) _offs();
  void qbuffer_resize(int i) {
    if (qbuffer.length < i) {
      auto backup = qbuffer;
      qbuffer = new char[max(65536, i)];
      qbuffer[0 .. backup.length] = backup;
    }
    _qbuffer() = qbuffer;
  }
  void append(string s) {
    qbuffer_resize(offs + s.length);
    qbuffer[offs .. offs+s.length] = s;
    offs += s.length;
    _offs() = offs;
  }
  foreach (entry; t) {
    static if (is(typeof(entry): string)) {
      append(entry);
    }
    else static if (is(typeof(entry): ulong)) {
      auto num = entry;
      if (!num) { append("0"); continue; }
      if (num == -0x8000_0000) { append("-2147483648"); }
      else {
        if (num < 0) { append("-"); num = -num; }
        
        // gotta do this left to right!
        static if (typeof(num).sizeof == 4) alias int IntType;
        else static if (typeof(num).sizeof == 8) alias long IntType;
        else static if (typeof(num).sizeof == 2) alias short IntType;
        else static if (typeof(num).sizeof == 1) alias byte IntType;
        else static assert(false, typeof(num).stringof);
        IntType ifact = 1;
        while (ifact <= num / 10) ifact *= 10;
        while (ifact) {
          int inum = num / ifact;
          char[1] ch;
          ch[0] = "0123456789"[inum];
          append(ch);
          num -= cast(long) inum * cast(long) ifact;
          ifact /= 10L;
        }
      }
    }
    else static if (is(typeof(entry[0]))) {
      append("[");
      bool first = true;
      foreach (element; entry) {
        if (first) first = false;
        else append(", ");
        qformat_append(element);
      }
      append("]");
    }
    else static if (is(typeof(fastcast!(Object) (entry)))) {
      auto obj = fastcast!(Object) (entry);
      append(obj.toString());
    }
    else static assert(false, "not supported in qformat: "~typeof(entry).stringof);
  }
}

string qformat(T...)(T t) {
  _offs() = 0;
  qformat_append(t);
  string qbuffer = *_qbuffer.ptr();
  int offs = *_offs.ptr();
  auto res = qbuffer[0 .. offs];
  qbuffer = qbuffer[offs .. $];
  _qbuffer() = qbuffer;
  return res;
}
