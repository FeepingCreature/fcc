module smtest;
import glsetup, opengl, std.c.math, std.c.time;

int fps, last_time;

float t = 0;

void drawScene() {
  glClear (GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);
  glLoadIdentity;
  glTranslatef (0, 0, -6);
  // glRotatef (t, 1, 0.1, 0);
  // glRotatef (180, 1, 0, 0);
  glRotatef (t, 0, 1, 0);
  t -= 1;
  (vec3f[auto~], vec3f[auto~]) cubedata;
  onExit { cubedata[0].free; cubedata[1].free; }
  void genCubeData() {
    alias points = cross ((0..2) x 3);
    alias cols = [for i ← 0..8: i / 8.0];
    static while int idx ← [
      0, 1, 3, 2,  4, 5, 7, 6, // top, bottom
      0, 1, 5, 4,  1, 3, 7, 5,  3, 2, 6, 7,  2, 0, 4, 6] { // sides
      cubedata[0] ~= vec3f (cols[idx] x 3);
      cubedata[1] ~= vec3f (points[idx]);
    }
  }
  genCubeData();
  void drawCube() {
    glEnableClientState GL_VERTEX_ARRAY;
    glEnableClientState GL_COLOR_ARRAY;
    glColorPointer (3, GL_FLOAT, size-of vec3f, cubedata[0].ptr);
    glVertexPointer (3, GL_FLOAT, size-of vec3f, cubedata[1].ptr);
    glDrawArrays (GL_QUADS, 0, cubedata[0].length);
  }
  
  glScalef (0.2 x 3);
  glTranslatef (0, 2 * sin(t / 64), 0);
  bool fun(vec3f v) {
    if v.length() > 10 return false;
    if (v.xy.length() < 4 || v.yz.length() < 4 || v.xz.length() < 4) return false;
    return true;
  }
  while auto vec ← [for x ← cross (-10 .. 10) x 3: vec3f(x)] if fun(vec) using glMatrix {
    glTranslatef vec;
    drawCube();
  }
  swap();
  fps ++;
  auto ct = time(time_t*:null);
  if ct != last_time {
    last_time = ct;
    writeln "FPS: $fps";
    fps = 0;
  }
}

int main(int argc, char** argv) {
  auto surf = setup-gl();
  while true {
    drawScene();
    if update(surf) quit(0);
  }
}
