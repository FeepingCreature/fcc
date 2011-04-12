module std.math;

import std.c.math;

vec3f cross3f(vec3f a, vec3f b) { return a.yzx * b.zxy - a.zxy * b.yzx; }

vec3f normalize3f(vec3f v) { return v / v.length; }

float angle3f(vec3f v, vec3f to, vec3f refer) {
  // yay, http://tomyeah.com/signed-angle-between-two-vectors3d-in-cc/
  auto v1 = v.cross3f(to) * refer;
  bool flipped = eval (v1.sum < 0);
  auto res = acosf((v*to).sum / sqrtf(v.selfdot * to.selfdot));
  // fudge
  if (flipped) res = -res;
  return res;
}

vec3f rotate3f(vec3f vec, vec3f axis, float angle) using vec {
  float u = axis.x, v = axis.y, w = axis.z;
  float uu = u*u, vv = v*v, ww = w*w;
  float v_w = vv + ww, u_w = uu + ww, u_v = uu + vv;
  float dd = (vec*axis).sum, cosa = cosf(angle), sina = sinf(angle);
  vec3f res = void;
  // pathologically slow to parse
  /*res = axis * dd
    + (vec * vec3f(v_w, u_w, u_v) + axis * (axis.yxx*(-vec.yxx) + axis.zzy * (-vec.zzy))) * cosa
    + (axis.zzy * vec3f (vec.(-y, x, -x)) + axis.yxx * vec3f(vec.(z, -z, y))) * sina;*/
  res.x = u*dd+(x*v_w+u*(v*(-y)+w*(-z))) * cosa + (w*(-y)+v*z) * sina;
  res.y = v*dd+(y*u_w+v*(u*(-x)+w*(-z))) * cosa + (w*x+u*(-z)) * sina;
  res.z = w*dd+(z*u_v+w*(u*(-x)+v*(-y))) * cosa + (v*(-x)+u*y) * sina;
  res /= axis.lensq;
  return res;
}

alias PI = 3.1415926538;
alias PI180 = PI/180.0;

float log(float f) { return logf f; }
float pow(float a, b) { return powf (a, b); }

float sin(float f) {
  short status;
  float local = f;
  asm "fld (%esp)";
  asm "fxam";
  asm "fstsw 6(%esp)"; // 4-aligned
  if (status & 0b0000_0101__0000_0000 == 0b101 << 8) { int i = 0; i /= i; } // infty
  asm "fsin";
  asm "fstsw 6(%esp)"; // also 4-aligned
  asm "fstp (%esp)";
  if (status & 0b0000_0100__0000_0000) { int i = 0; i /= i; }
  return local;
}

float cos(float f) {
  short status;
  float local = f;
  asm "fld (%esp)";
  asm "fxam";
  asm "fstsw 6(%esp)"; // 4-aligned
  if (status & 0b0000_0101__0000_0000 == 0b101 << 8) { int i = 0; i /= i; } // infty
  asm "fcos";
  asm "fstsw 6(%esp)"; // 4-aligned
  asm "fstp (%esp)";
  if (status & 0b0000_0100__0000_0000) { int i = 0; i /= i; }
  return local;
}

float sqrtf(float f) {
  short status;
  float local = f;
  asm "fld (%esp)";
  asm "fsqrt";
  asm "fxam";
  asm "fstsw 6(%esp)";
  asm "fstp (%esp)";
  if (status & 0b0000_0101__0000_0000 == (0b101 << 8)) { int i = 0; i /= i; } // infty
  return local;
}
  
vec2f half(vec2f a, b) return (a + b) / 2;
vec3f half(vec3f a, b) return (a + b) / 2;
vec4f half(vec4f a, b) return (a + b) / 2;

float min(float a, b) return [a, b][eval a > b];
float max(float a, b) return [a, b][eval a < b];

bool isNan(float f) {
  int i = *int*:&f;
  return eval (i & 0x7fff_ffff) > 0x7f80_0000;
}
