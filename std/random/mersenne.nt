module std.random.mersenne;

import std.random.base;

class MersenneTwister : IRandom {
  int x 624  state;
  int index;
  void init(int seed = 23) {
    state[0] = seed;
    for int i <- 1..state.length
      state[i] = 1812433253 * (state[i-1] xor (state[i-1] << 30)) + i;
  }
  void generateNumbers() {
    for int i <- 0..state.length {
      int y = state[i] & 0x8000_0000 | state[(i+1)%$] & 0x7fff_ffff;
      state[i] = state[(i + 397)%$] xor (y >> 1);
      if (y & 1) state[i] xor= 0x9908_b0df;
    }
  }
  int rand() {
    if !index generateNumbers;
    int y = state[index++];
    index %= 624;
    y xor= (y >> 11);
    y xor= (y << 7) & 0x9d2c_5680;
    y xor= (y << 15) & 0xefc6_0000;
    y xor= (y >> 18);
    return y;
  }
  void init(IRandom ir) {
    for int i <- 0..state.length
      state[i] = ir.rand();
  }
}

void init() {
  engines ~= (
    delegate IRandom(int s) { return new MersenneTwister s; },
    delegate IRandom(IRandom ir) { return new MersenneTwister ir; },
    4);
}
