module quickformat;

import tools.threads, tools.base;
import casts;

extern(C) Stuple!(string, int)* get_qbuffer_ptr();

void qbuffer_resize_internal(int i, string* qbufferp, int* offsp) {
  if ((*qbufferp).length < i) {
    auto backup = (*qbufferp);
    // there's no chance to free this anyway, so don't let the gc bother with it
    // otherwise the get_qbuffer_ptr will fail because we keep reference in C space
    // (*qbufferp) = new char[max(65536, i)];
    auto newlen = max(i, 65536);
    (*qbufferp) = (cast(char*) std.c.stdlib.malloc(newlen))[0..newlen];
    (*qbufferp)[0 .. backup.length] = backup;
  }
}

void qappend(string[] args...) {
  auto qp = get_qbuffer_ptr();
  string qbuffer; int offs;
  ptuple(qbuffer, offs) = *qp;
  
  int total_len;
  foreach (arg; args) total_len += arg.length;
  qbuffer_resize_internal(offs + total_len, &qbuffer, &offs);
  
  foreach (arg; args) {
    qbuffer[offs .. offs + arg.length] = arg;
    offs += arg.length;
  }
  
  *qp = stuple(qbuffer, offs);
}

uint[] stepsize_int = [1, 100, 10_000, 1_000_000, 100_000_000];
ulong[] stepsize_long = [1UL, 100UL, 10_000UL, 1_000_000UL, 100_000_000UL, 10_000_000_000UL,
  1_000_000_000_000UL, 100_000_000_000_000UL, 10_000_000_000_000_000UL, 1_000_000_000_000_000_000UL];

void qformat_append(T...)(T t) {
  string[T.length] prestuff;
  // do the objects up-front because they might call qformat recursively
  foreach (i, entry; t) {
    static if (is(typeof(entry): string)) { }
    else static if (is(typeof(entry): ulong)) { }
    else static if (is(typeof(entry[0]))) { }
    else static if (is(typeof(cast(Object) entry))) {
      auto obj = fastcast!(Object) (entry);
      if (obj) prestuff[i] = obj.toString();
    }
  }
  foreach (i, entry; t) {
    static if (is(typeof(entry): string)) {
      qappend(entry);
    }
    else static if (is(typeof(entry) == bool)) {
      if (entry) qappend("true");
      else qappend("false");
    }
    else static if (is(typeof(entry): ulong)) {
      auto num = entry;
      if (!num) { qappend("0"[]); continue; }
      if (num == -0x8000_0000) { qappend("-2147483648"[]); }
      else {
        if (num < 0) { qappend("-"[]); num = -num; }
        
        static if (typeof(num).sizeof == 8) alias long IntType;
        else alias int IntType;
        int steps;
        static if (typeof(num).sizeof == 8) alias stepsize_long stepsize;
        else alias stepsize_int stepsize;
        while (steps < stepsize.length && stepsize[steps] <= num) steps ++;
        steps --;
        {
          IntType ifact = stepsize[steps];
          int inum = num / ifact;
          if (inum < 10) {
            char[1] ch;
            ch[0] = "0123456789"[inum];
            qappend(ch[]);
          } else {
            char[2] ch;
            ch[0] = "0000000000111111111122222222223333333333444444444455555555556666666666777777777788888888889999999999"[inum];
            ch[1] = "0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"[inum];
            qappend(ch[]);
          }
          num -= cast(IntType) inum * ifact;
        }
        for (int k = steps - 1; k >= 0; --k) {
          IntType ifact = stepsize[k];
          int inum = num / ifact;
          char[2] ch;
          ch[0] = "0000000000111111111122222222223333333333444444444455555555556666666666777777777788888888889999999999"[inum];
          ch[1] = "0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789"[inum];
          qappend(ch);
          num -= cast(IntType) inum * ifact;
        }
      }
    }
    else static if (is(typeof(entry[0]))) {
      qappend("["[]);
      bool first = true;
      foreach (element; entry) {
        if (first) first = false;
        else qappend(", "[]);
        qformat_append(element);
      }
      qappend("]"[]);
    }
    else static if (is(typeof(cast(Object) entry))) {
      auto obj = fastcast!(Object) (entry);
      if (obj) qappend(prestuff[i]); // use cache from earlier
      else { qappend(typeof(entry).stringof); qappend(":null"); }
    }
    else static assert(false, "not supported in qformat: "~typeof(entry).stringof);
  }
}

string qfinalize() {
  auto qp = get_qbuffer_ptr();
  string qbuffer; int offs;
  ptuple(qbuffer, offs) = *qp;
  auto res = qbuffer[0 .. offs];
  qbuffer = qbuffer[offs .. $];
  *qp = stuple(qbuffer, 0);
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
