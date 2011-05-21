module simplex;

int[] perm, mperm; // perm mod 12
vec3i x 12 grad3;

bool setupPerm;

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
  setupPerm = true;
  (perm, mperm) = (new int[] 256) x 2;
  int seed = 34;
  auto gen = new KISS;
  gen.seed(seed);
  int x 256 firstPerm;
  for int i <- 0..256 {
    perm[i] = (gen.rand() & 0x7fff_ffff) % 256;
    mperm[i] = perm[i] % 12;
  }
  /*for int i <- 0..256 {
    for int k <- 0..256 {
      int id = i * 256 + k;
      perm[id] = firstPerm[(firstPerm[i] + k) % 256];
      mperm[id] = perm[id] % 12;
    }
  }*/
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
  if !setupPerm permsetup;
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
  // gi[0] = mperm[(ii      + perm[jj     ]) & 255];
  // gi[1] = mperm[(ii + i1 + perm[jj + j1]) & 255];
  // gi[2] = mperm[(ii +  1 + perm[jj +  1]) & 255];
  gi[0] = mperm[jj * 256 + ii];
  gi[1] = mperm[(jj + j1) * 256 + (ii + i1)];
  gi[2] = mperm[(jj + 1) * 256 + (ii + 1)];
  
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
  int x 4  gi = void;
  int mask = void;
  vec3f v0 = void;
  if !setupPerm permsetup;
  
  vsum = v + (v.sum / 3.0f);
  // copypasted from fastfloor3f
  xmm[4] = vsum;
  asm `cvttps2dq %xmm4, %xmm5`;
  asm `psrld $31, %xmm4`;
  asm `psubd %xmm4, %xmm5`;
  auto indices = vec3i:xmm[5];
  vs[0] = v - indices      + vec3f(indices.sum / 6.0f);
  xmm[6] = vec4f:vs[0];
  vs[1] = xmm[6] + vec4f(1.0f / 6);
  vs[2] = xmm[6] + vec4f(2.0f / 6);
  vs[3] = xmm[6] + vec4f(-1 + 3.0f / 6);
  xmm[4] = xmm[6].xxy;
  xmm[5] = xmm[6].yzz;
  // this is correct, I worked it out
  mask = [0b100_110, 0b010_110, 0, 0b010_011, 0b100_101, 0, 0b001_101, 0b001_011][(eval xmm[4] < xmm[5]) & 0b0111];
  // if (v0.x < v0.y) {
  //   if (v0.y < v0.z) {
  //     mask = 0b001_011; // X Y Z
  //   } else if (v0.x < v0.z) {
  //     mask = 0b010_011; // X Z Y
  //   } else {
  //     mask = 0b010_110; // Z X Y
  //   }
  // } else {
  //   if (v0.y < v0.z) {
  //     if (v0.x < v0.z) {
  //       mask = 0b001_101; // Y X Z
  //     } else {
  //       mask = 0b100_101; // Y Z X
  //     }
  //   } else {
  //     mask = 0b100_110; // Z Y X
  //   }
  // }
  auto offs1 = vec3i((mask >> 5)    , (mask >> 4) & 1, (mask >> 3) & 1);
  auto offs2 = vec3i((mask >> 2) & 1, (mask >> 1) & 1, (mask >> 0) & 1);
  // auto index = (eval xmm[4] < xmm[5]) & 0b0111;
  // // auto offs1 = [vec3i(1,0,0), vec3i(0,1,0), vec3i(0), vec3i(0,1,0), vec3i(1,0,0), vec3i(0), vec3i(0,0,1), vec3i(0,0,1)][index];
  // // auto offs2 = [vec3i(1,1,0), vec3i(1,1,0), vec3i(0), vec3i(0,1,1), vec3i(1,0,1), vec3i(0), vec3i(1,0,1), vec3i(0,1,1)][index];
  // auto offs1 = vec3i([1, 0, 0, 0, 1, 0, 0, 0][index], [0, 1, 0, 1, 0, 0, 0, 0][index], [0, 0, 0, 0, 0, 0, 1, 1][index]);
  // auto offs2 = vec3i([1, 1, 0, 0, 1, 0, 1, 0][index], [1, 1, 0, 1, 0, 0, 0, 1][index], [0, 0, 0, 1, 1, 0, 1, 1][index]);
  vs[1] -= vec3f(offs1);
  vs[2] -= vec3f(offs2);
  auto ii = indices.x, jj = indices.y, kk = indices.z;
  alias i1 = offs1.x, i2 = offs2.x,
        j1 = offs1.y, j2 = offs2.y,
        k1 = offs1.z, k2 = offs2.z;
  {
    auto lperm = perm.ptr;
    auto mperm = mperm.ptr;
    gi = [
      mperm[(lperm[(lperm[(kk   )&0xff]+jj   )&0xff]+ii   )&0xff],
      mperm[(lperm[(lperm[(kk+k1)&0xff]+jj+j1)&0xff]+ii+i1)&0xff],
      mperm[(lperm[(lperm[(kk+k2)&0xff]+jj+j2)&0xff]+ii+i2)&0xff],
      mperm[(lperm[(lperm[(kk+1 )&0xff]+jj+1 )&0xff]+ii+1 )&0xff]
    ];
    // gi = [
    //   mperm[(lperm[(((kk   )&0xff) << 8 + jj   )&0xffff] << 8 + ii   )&0xffff],
    //   mperm[(lperm[(((kk+k1)&0xff) << 8 + jj+j1)&0xffff] << 8 + ii+i1)&0xffff],
    //   mperm[(lperm[(((kk+k2)&0xff) << 8 + jj+j2)&0xffff] << 8 + ii+i2)&0xffff],
    //   mperm[(lperm[(((kk+ 1)&0xff) << 8 + jj+ 1)&0xffff] << 8 + ii+ 1)&0xffff]
    // ];
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
