module cltest;

c_include "CL/cl.h";
import sys;

void main() {
  int ids;
  clGetPlatformIDs(0, cl_platform_id*:null, &ids);
  auto platforms = new cl_platform_id[ids];
  clGetPlatformIDs(ids, platforms.ptr, cl_uint*:null);
  writeln "$ids platform(s). ";
  int i; cl_platform_id platform;
  while (i, platform) <- [for i <- 0..ids: (i, platforms[i])] {
    string info; int enum;
    while (info, enum) <- [
     ("Profile"[], CL_PLATFORM_PROFILE),
     ("Version"[], CL_PLATFORM_VERSION),
     ("Name"[],    CL_PLATFORM_NAME),
     ("Vendor"[],  CL_PLATFORM_VENDOR),
     ("Extensions"[], CL_PLATFORM_EXTENSIONS)]
    {
      int size;
      clGetPlatformInfo (platform, enum, 0, null, &size);
      auto store = new char[size];
      onExit store.free();
      clGetPlatformInfo (platform, enum, size, store.ptr, int*:null);
      writeln "$i: $info = $store";
    }
    int devs;
    clGetDeviceIDs (platform, CL_DEVICE_TYPE_ALL, 0, cl_device_id*:null, &devs);
    if (!devs) {
      writeln "No devices. ";
    } else {
      auto devlist = new cl_device_id[devs];
      onExit devlist.free;
      clGetDeviceIDs (platform, CL_DEVICE_TYPE_ALL, devs, devlist.ptr, int*:null);
      int k; cl_device_id dev;
      string devinfo; int enum2;
      while ((k, dev), (devinfo, enum2)) <- cross (
        [for k <- 0..devs: (k, devlist[k])],
        [("Extensions"[], CL_DEVICE_EXTENSIONS),
        ("Name"[], CL_DEVICE_NAME),
        ("Profile"[], CL_DEVICE_PROFILE),
        ("Vendor"[], CL_DEVICE_VENDOR),
        ("Version"[], CL_DEVICE_VERSION),
        ("DriverVersion"[], CL_DRIVER_VERSION)])
      {
        int size;
        clGetDeviceInfo (dev, enum2, 0, null, &size);
        auto devstore = new char[size];
        onExit devstore.free;
        clGetDeviceInfo (dev, enum2, size, devstore.ptr, int*:null);
        writeln "  $k: $devinfo = $devstore ($size)";
      }
    }
  }
}
