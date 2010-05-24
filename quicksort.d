module quicksort;

// Marsaglia's KISS RNG, hopefully not patented :p
class KISS {
  int x = 123456789, y = 362436000, z = 521288629, c = 7654321; // seeds
  invariant {
    assert(y, "y must never be set to zero! ");
    assert(c, "c shouldn't be zero itself");
  }
  uint opCall() {
    ulong a = 698769069UL;
    x = 69069 * x + 12345;
    y ^= (y << 13); y ^= (y >> 17); y ^= (y << 5);
    ulong t = a * z + c;
    assert(t, "this shouldn't be 0 either! ");
    c = (t >> 32);
    z = t;
    return x + y + z;
  }
}

// shared is good .. we don't care about cross-processor pollution
KISS global_rng;
static this() { global_rng = new KISS; }

// inplace
import tools.base: swap;
void qsort(T, C)(T[] array, C smaller, void delegate(ref T, ref T) swap = null) {
  if (!swap) swap = (ref T a, ref T b) { .swap(a, b); };
  if (array.length == 0 || array.length == 1) return;
  if (array.length == 2) {
    if (smaller(array[1], array[0])) swap(array[0], array[1]);
    return;
  }
  auto pivot = array[global_rng() % $];
  auto unsorted = array;
  int left = 0, right = array.length;
  while (true) {
    while (unsorted.length && smaller(unsorted[0], pivot)) { unsorted = unsorted[1 .. $]; left ++; }
    while (unsorted.length && smaller(pivot, unsorted[$-1])) { unsorted = unsorted[0 .. $-1]; right --; }
    if (unsorted.length < 2) break;
    swap(unsorted[0], unsorted[$-1]);
    unsorted = unsorted[1 .. $-1];
    left ++; right --;
  }
  array[0 .. left].qsort(smaller);
  array[right .. $].qsort(smaller);
}

/*
import tools.log;
void main() {
  int[] test;
  for (int i = 0; i < 100; ++i) test ~= global_rng() % 100;
  logln(" original ", test);
  qsort(test, (int a, int b) { return a < b; });
  logln("   sorted ", test);
}
*/
