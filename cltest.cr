module cltest;

c_include "CL/cl.h";
import sys;

void main() {
  int ids;
  clGetPlatformIDs(0, cl_platform_id*:null, &ids);
  auto platforms = new cl_platform_id[ids];
  clGetPlatformIDs(ids, platforms.ptr, cl_uint*:null);
  writeln "$ids platform(s). ";
  int i, enum; string info;
  while (i, (info, enum)) <- cross (
    0..ids,
    [("Profile"[], CL_PLATFORM_PROFILE),
     ("Version"[], CL_PLATFORM_VERSION),
     ("Name"[],    CL_PLATFORM_NAME),
     ("Vendor"[],  CL_PLATFORM_VENDOR),
     ("Extensions"[], CL_PLATFORM_EXTENSIONS)])
  {
    int size;
    clGetPlatformInfo(platforms[i], enum, 0, null, &size);
    auto store = new char[size];
    onExit store.free();
    clGetPlatformInfo(platforms[i], enum, size, store.ptr, int*:null);
    writeln "$i: $info = $store";
  }
}
