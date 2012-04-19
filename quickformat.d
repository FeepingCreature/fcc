module quickformat;

import tools.threads, tools.base;
import casts;

TLS!(Stuple!(string, int)) _qbuffer;
static this() { New(_qbuffer); }

void qbuffer_resize(int i) {
  string qbuffer; int offs;
  ptuple(qbuffer, offs) = *_qbuffer();
  if (qbuffer.length < i) {
    auto backup = qbuffer;
    qbuffer = new char[max(65536, i)];
    qbuffer[0 .. backup.length] = backup;
  }
  *_qbuffer() = stuple(qbuffer, offs);
}

void qappend(string[] args...) {
  string qbuffer; int offs;
  ptuple(qbuffer, offs) = *_qbuffer();
  
  int total_len;
  foreach (arg; args) total_len += arg.length;
  qbuffer_resize(offs + total_len);
  ptuple(qbuffer, offs) = *_qbuffer();
  
  foreach (arg; args) {
    qbuffer[offs .. offs + arg.length] = arg;
    offs += arg.length;
  }
  
  _qbuffer()._1 = offs;
}

void qformat_append(T...)(T t) {
  foreach (entry; t) {
    static if (is(typeof(entry): string)) {
      qappend(entry);
    }
    else static if (is(typeof(entry): ulong)) {
      auto num = entry;
      if (!num) { qappend("0"); continue; }
      if (num == -0x8000_0000) { qappend("-2147483648"); }
      else {
        if (num < 0) { qappend("-"); num = -num; }
        
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
          qappend(ch);
          num -= cast(long) inum * cast(long) ifact;
          ifact /= 10L;
        }
      }
    }
    else static if (is(typeof(entry[0]))) {
      qappend("[");
      bool first = true;
      foreach (element; entry) {
        if (first) first = false;
        else qappend(", ");
        qformat_append(element);
      }
      qappend("]");
    }
    else static if (is(typeof(fastcast!(Object) (entry)))) {
      auto obj = fastcast!(Object) (entry);
      qappend(obj.toString());
    }
    else static assert(false, "not supported in qformat: "~typeof(entry).stringof);
  }
}

string qfinalize() {
  string qbuffer; int offs;
  ptuple(qbuffer, offs) = *_qbuffer();
  auto res = qbuffer[0 .. offs];
  qbuffer = qbuffer[offs .. $];
  *_qbuffer() = stuple(qbuffer, 0);
  return res;
}

string qformat(T...)(T t) {
  qformat_append(t);
  return qfinalize();
}

string qjoin(string[] args) {
  foreach (arg; args)
    qappend(arg);
  return qfinalize();
}
