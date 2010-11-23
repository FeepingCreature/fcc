module opengl;

c_include "GL/gl.h";
c_include "GL/glu.h";

extern(C) void* glXGetProcAddress(char*);

alias glBindBufferARB = *void function(GLenum, GLuint): glXGetProcAddress("glBindBufferARB");
alias glBufferDataARB = *void function(GLenum, GLsizei, void*, GLenum): glXGetProcAddress("glBufferDataARB");
alias glGenBuffersARB = *void function(GLsizei, GLuint*): glXGetProcAddress("glGenBuffersARB");

context Triangles {
  alias onUsing = glBegin GL_TRIANGLES;
  alias onExit = glEnd;
}

context Quads {
  alias onUsing = glBegin GL_QUADS;
  alias onExit = glEnd;
}

context glMatrix {
  alias onUsing = glPushMatrix();
  alias onExit  = glPopMatrix ();
}
