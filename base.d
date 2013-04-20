module base;

import tools.base, quickformat;

const nativeIntSize = 4, nativePtrSize = 4;

int xpar = -1; // for debugging. see xpar_bisect.nt

string path_prefix, platform_prefix;

bool isWindoze() {
  return platform_prefix.find("mingw"[]) != -1;
}

bool isARM() {
  return !!platform_prefix.startsWith("arm-"[]);
}

version(Windows) static this() { platform_prefix = "i686-mingw32-"; }

extern(C) int atoi(char*);
int my_atoi(string s) {
  auto mew = qformat(s, "\x00"[]);
  return atoi(mew.ptr);
}

const esp_alignment_delta = 8; // call, push ebp
