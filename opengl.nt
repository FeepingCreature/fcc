module opengl;

c_include "GL/gl.h";
c_include "GL/glu.h";

platform(i686-mingw32) <<EOF
  extern(Windows) void* wglGetProcAddress(char*);
  template lookupFun(T) <<EO2
    _markStdCall T lookupFun(char* c) { return _markStdCall T:wglGetProcAddress(c); }
  EO2
EOF

platform(default) <<EOF
  c_include "GL/glx.h";
  extern(C) void* glXGetProcAddress(char*);
  template lookupFun(T) <<EO2
    T lookupFun(char* c) { return T:glXGetProcAddress(c); }
  EO2
EOF

alias glBindBufferARB = *lookupFun!void function(GLenum, GLuint) "glBindBufferARB";
alias glBufferDataARB = *lookupFun!void function(GLenum, GLsizei, void*, GLenum) "glBufferDataARB";
alias glGenBuffersARB = *lookupFun!void function(GLsizei, GLuint*) "glGenBuffersARB";
alias glDeleteBuffersARB = *lookupFun!void function(GLsizei, GLuint*) "glDeleteBuffersARB";

context Triangles {
  alias onUsing = glBegin GL_TRIANGLES;
  alias onExit = glEnd;
}

context Quads {
  alias onUsing = glBegin GL_QUADS;
  alias onExit = glEnd;
}

context QuadStrip {
  alias onUsing = glBegin GL_QUAD_STRIP;
  alias onExit = glEnd;
}

context glMatrix {
  alias onUsing = glPushMatrix();
  alias onExit  = glPopMatrix ();
}
