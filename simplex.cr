module simplex;

import std.c.fenv, std.c.stdlib;

int[] perm;
int[3][12] grad3;

float dot(int[3] whee, float a, float b) {
  return whee[0] * a + whee[1] * b;
}

float noise2(vec2f f) {
  if !perm.length {
    perm ~= [for 0..256: rand() % 256].eval;
    perm ~= perm;
    int i;
    alias values = [1,1,0,-1, 1,0,1,-1, 0,-1,-1,0, 1,0,1,-1, 0,1,1,0, -1,-1,0,-1, 0,1,1,0, -1,1,0,1, -1,0,-1,-1];
    while ((int k, int l), int idx) ← zip (cross (0..12, 0..3), 0..-1) {
      grad3[k][l] = values[idx];
    }
  }
  float sqrt3 = sqrtf(3);
  float f2 = 0.5 * (sqrt3 - 1), g2 = (3 - sqrt3) / 6;
  fesetround(1024);
  float[3] n = void;
  
  float s = (f.x + f.y) * f2;
  int i = int:(f.x + s), j = int:(f.y + s);
  
  float t = (i + j) * g2;
  vec2f[3] xy;
  xy[0] = f - ((vec2i(i,j)) - vec2f(t));
  
  int i1, j1;
  if xy[0].x > xy[0].y i1 = 1;
  else j1 = 1;
  
  {
    auto temp = 1 - 2 * g2;
    xy[1] = xy[0] - (vec2i(i1, j1)) + vec2f (g2);
    xy[2] = xy[0] - vec2f(temp);
  }
  int ii = i & 255, jj = j & 255;
  
  int[3] gi = void;
  gi[0] = perm[ii + perm[jj]] % 12;
  gi[1] = perm[ii + i1 + perm[jj + j1]] % 12;
  gi[2] = perm[ii + 1  + perm[jj + 1 ]] % 12;
  
  for (int k = 0; k < 3; ++k) {
    float ft = 0.5 - xy[k].x*xy[k].x - xy[k].y*xy[k].y;
    if ft < 0 n[k] = 0;
    else {
      ft = ft * ft;
      n[k] = ft * ft * dot(grad3[gi[k]], xy[k]);
    }
  }
  return 0.5 + 35 * (n[0] + n[1] + n[2]);
}
