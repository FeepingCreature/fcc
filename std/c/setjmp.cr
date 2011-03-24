module std.c.setjmp;

// c_include "setjmp.h";

alias __jmp_buf = size_t[8];
struct __sigset_t {
  size_t[1024 / (8*size-of size_t)] __val;
}

struct jmp_buf {
  __jmp_buf __jmpbuf;
  int __mask_was_saved;
  __sigset_t __saved_mask;
}

extern(C) {
  void longjmp(jmp_buf* env, int val);
  int setjmp(jmp_buf* env);
}
