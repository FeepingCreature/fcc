module mob;

import sys;

struct LiteralHolder {
  int i;
  int call() { return i; }
}

template Alloc(T) <<EOH
  T* Alloc() {
    return cast(T*) sys.mem.malloc(T.sizeof);
  }
EOH

int delegate() lit(int i) {
  auto res = Alloc!LiteralHolder();
  printf("res is %p, call is %p %p\n", res, &res.call);
  res.i = i;
  return &res.call;
}

void main() {
  int A(int k, int delegate() x1, x2, x3, x4, x5) {
    int B() {
      k --;
      return A(k, &B, x1, x2, x3, x4);
    }
    writeln("x4 is $$typeof(x4).stringof");
    auto i = x4();
    // if (k <= 0) return x4() + x5();
    // else return B();
  }
  auto foo = lit(0);
  writeln("foo is");
  printf("::%p %p\n", foo.fun, foo.data);
  writeln("$$foo()");
  auto res = A(10, lit(1), lit(-1), lit(-1), lit(1), lit(0));
  writeln("$res");
}
