module simplex;

import std.c.fenv, std.c.stdlib;

int[~] perm;
vec3i x 12 grad3;

float dot2(int x 4 whee, float a, float b) {
  return whee[0] * a + whee[1] * b;
}

class KISS {
  int x, y, z, w, carry, k, m;
  void init() { (x, y, z, w, carry) = (1, 2, 4, 8, 0); }
  void seed(int i) {
    (x, y, z, w) = (i | 1, i | 2, i | 4, i | 8);
    carry = 0;
  }
  int rand() {
    x = x * 69069 + 1;
    y xor= y << 13;
    y xor= y >> 17;
    y xor= y << 5;
    k = (z >> 2) + (w >> 3) + (carry >> 2);
    m = w + w + z + carry;
    z = w;
    w = m;
    carry = k >> 30;
    return x + y + w;
  }
}

void permsetup() {
  int seed = 34;
  auto gen = new KISS;
  gen.seed(seed);
  perm ~= [for 0..256: gen.rand() % 256].eval;
  for (int i <- 0..256) if (perm[i] < 0) perm[i] = -perm[i];
  perm ~= perm[];
  int i;
  alias values = [1, 1, 0,
                 -1, 1, 0,
                  1,-1, 0,
                 -1,-1, 0,
                 
                  1, 0, 1,
                 -1, 0, 1,
                  1, 0,-1,
                 -1, 0,-1,
                 
                  0, 1, 1,
                  0,-1, 1,
                  0, 1,-1,
                  0,-1,-1];
  while ((int k, int l), int idx) <- zip (cross (0..12, 0..3), 0..-1) {
    grad3[k][l] = values[idx];
  }
}

float noise2(vec2f f) {
  if !perm.length permsetup;
  alias sqrt3 = sqrtf(3);
  alias f2 = 0.5 * (sqrt3 - 1);
  alias g2 = (3 - sqrt3) / 6;
  float x 3  n = void;
  
  float s = (f.x + f.y) * f2;
  int i = fastfloor(f.x + s), j = fastfloor(f.y + s);
  
  float t = (i + j) * g2;
  vec2f x 3  xy;
  xy[0] = f - (vec2i(i,j) - vec2f(t));
  
  int i1, j1;
  if xy[0].x > xy[0].y i1 = 1;
  else j1 = 1;
  
  {
    auto temp = 1 - 2 * g2;
    xy[1] = xy[0] - vec2i(i1, j1) + vec2f (g2);
    xy[2] = xy[0] - vec2f(temp);
  }
  int ii = i & 255, jj = j & 255;
  
  int x 3  gi = void;
  gi[0] = perm[ii + perm[jj]] % 12;
  gi[1] = perm[ii + i1 + perm[jj + j1]] % 12;
  gi[2] = perm[ii + 1  + perm[jj + 1 ]] % 12;
  
  for (int k = 0; k < 3; ++k) {
    float ft = 0.5 - xy[k].x*xy[k].x - xy[k].y*xy[k].y;
    if ft < 0 n[k] = 0;
    else {
      ft = ft * ft;
      n[k] = ft * ft * dot2(grad3[gi[k]], xy[k]);
    }
  }
  return 0.5 + 35 * (n[0] + n[1] + n[2]);
}

double sumval;
int count;

void time-it(string t, void delegate() dg) {
  // calibrate
  int from1, to1, from2, to2;
  from1 = rdtsc[1];
  delegate void() { } ();
  to1 = rdtsc[1];
  // measure
  from2 = rdtsc[1];
  dg();
  to2 = rdtsc[1];
  auto delta = (to2 - from2) - (to1 - from1);
  if !count sumval = 0;
  sumval += delta; count += 1;
  writeln "$t: $delta, average $(sumval / count)";
}

void testAlign(string name, void* p) {
  if !(int:p & 0b1111) writeln "$name: 16-aligned";
  else if !(int:p & 0b111) writeln "$name: 8-aligned";
  else if !(int:p & 0b11) writeln "$name: 4-aligned";
  else writeln "$name: not aligned";
}

float noise3(vec3f v) {
  vec3f x 4  vs = void;
  vec3f vsum = void;
  vec3i indices = void;
  int x 4  gi = void;
  int mask = void;
  vec3f v0 = void;
  if !perm.length permsetup;
  
  vsum = v + (v.sum / 3.0f);
  fastfloor3f (vsum, &indices);
  vs[0] = v - indices      + (indices.sum / 6.0f);
  vs[1] = vs[0]            + vec3f(1.0f / 6);
  vs[2] = vs[0]            + vec3f(2.0f / 6);
  vs[3] = vs[0]       + vec3f(-1 + 3.0f / 6);
  xmm[4] = vs[0].xxy;
  xmm[5] = vs[0].yzz;
  // this is correct, I worked it out
  mask = [0b100_110, 0b010_110, 0, 0b010_011, 0b100_101, 0, 0b001_101, 0b001_011][(eval xmm[4] < xmm[5]) & 0b0111];
  /*if (v0.x < v0.y) {
    if (v0.y < v0.z) {
      mask = 0b001_011; // X Y Z
    } else if (v0.x < v0.z) {
      mask = 0b010_011; // X Z Y
    } else {
      mask = 0b010_110; // Z X Y
    }
  } else {
    if (v0.y < v0.z) {
      if (v0.x < v0.z) {
        mask = 0b001_101; // Y X Z
      } else {
        mask = 0b100_101; // Y Z X
      }
    } else {
      mask = 0b100_110; // Z Y X
    }
  }*/
  auto offs1 = vec3i((mask >> 5)    , (mask >> 4) & 1, (mask >> 3) & 1);
  auto offs2 = vec3i((mask >> 2) & 1, (mask >> 1) & 1, (mask >> 0) & 1);
  vs[1] -= vec3f(offs1);
  vs[2] -= vec3f(offs2);
  (int ii, int jj, int kk) = indices.(x & 255, y & 255, z & 255);
  alias i1 = offs1.x, i2 = offs2.x,
        j1 = offs1.y, j2 = offs2.y,
        k1 = offs1.z, k2 = offs2.z;
  {
    auto lperm = perm.ptr;
    gi[0] = lperm[lperm[lperm[kk   ]+jj   ]+ii   ] % 12;
    gi[1] = lperm[lperm[lperm[kk+k1]+jj+j1]+ii+i1] % 12;
    gi[2] = lperm[lperm[lperm[kk+k2]+jj+j2]+ii+i2] % 12;
    gi[3] = lperm[lperm[lperm[kk+1 ]+jj+1 ]+ii+1 ] % 12;
  }
  vec3f current = void;
  vec4f factors = void, res = void;
  auto pair = [1f, -1f, -1f];
  while (int c <- 0..4) {
    current = vs[c];
    current *= current;
    factors[c] = 0.6f - current.sum;
    current = vs[c];
    if (factors[c] >= 0) {
      auto id = gi[c];
      res[c] = (current[id >> 3] * pair[id&1]) + (current[((id >> 2) | (id >> 3)) & 1 + 1] * pair[id&2]);
    } else {
      factors[c] = 0;
      res[c] = 0;
    }
  }
  xmm[4] = factors;
  xmm[4] *= xmm[4];
  xmm[4] *= xmm[4];
  res *= xmm[4];
  return 0.5f + 16.0f*res.sum;
}
