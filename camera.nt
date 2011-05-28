module camera;

import std.math, opengl;

interface Camera {
  void gl-setup();
}

class PerspectiveCam : Camera {
  float fov, zNear, zFar, aspect;
  void init() {
    zNear = 0.01f;
    zFar = 100f;
    fov = 45f;
    aspect = 1f;
  }
  void gl-setup() {
    glMatrixMode GL_PROJECTION;
    glLoadIdentity;
    gluPerspective (fov, aspect, zNear, zFar);
  }
}

template WorldCam(T) << EOF
  class WorldCam : T {
    vec3f up, pos, lookat;
    alias dir = lookat - pos;
    vec3f setDir(vec3f v) { lookat = pos + v; return lookat; }
    void init() {
      super.init();
      (up, pos) = (vec3f.Y, vec3f(0));
      setDir -vec3f.Z;
    }
    void gl-setup() {
      super.gl-setup();
      glMatrixMode GL_MODELVIEW;
      glLoadIdentity;
      auto dirz = dir;
      dirz.z = -dirz.z;
      auto left = up.cross3f(dirz).normalize3f(), up = dirz.cross3f(left).normalize3f();
      (vec3f.Y.angle3f(up, left) / PI180).glRotatef vec3f.X;
      (vec3f.X.angle3f(left, up) / PI180).glRotatef vec3f.Y;
      glTranslatef (-pos);
    }
  }
EOF

template EgoCam(T) << EOF
  class EgoCam : T {
    vec3f pos;
    float turnX, turnY;
    void init(vec3f p, float x, y) { (pos, turnX, turnY) = (p, x, y); super.init(); }
    void init() { init(vec3f(0), 0, 0); }
    void turn-left(float f) { turnX += f; }
    alias lowlimit = -PI / 2 + 0.1;
    alias highlimit = PI / 2 - 0.1;
    void turn-up(float f) { turnY -= f; if (turnY < lowlimit) turnY = lowlimit; if (turnY > highlimit) turnY = highlimit; }
    alias dir = vec3f.Z.rotate3f(vec3f.X, turnY).rotate3f(vec3f.Y, turnX);
    alias left = vec3f.Y.cross3f(dir).normalize3f();
    void gl-setup() {
      super.gl-setup();
      glMatrixMode GL_MODELVIEW;
      glLoadIdentity;
      auto dirz = dir; dirz.z = -dirz.z;
      auto left = vec3f.Y.cross3f(dirz).normalize3f(), up = dirz.cross3f(left).normalize3f();
      (vec3f.Y.angle3f(up, left) / PI180).glRotatef vec3f.X;
      (vec3f.X.angle3f(left, up) / PI180).glRotatef vec3f.Y;
      glTranslatef (-pos);
    }
  }
EOF
