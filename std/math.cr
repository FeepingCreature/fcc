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
