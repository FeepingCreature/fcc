module cltest;

c_include "CL/cl.h";
import sys;

extern(C) cl_context clCreateContextFromType(
  cl_context_properties *properties,
  cl_device_type device_type,
  void function(char* errinfo, void* private_info, size_t cb, void* user_data) pfn_notify,
  void* user_data, cl_int* errcode_ret);

class ContextDelegateHolder {
  void delegate(char*, void*, size_t) dg;
  void call(char* errinfo, void* private_info, size_t cb) {
    dg(errinfo, private_info, cb);
  }
}

void callHolder(char* a, void* b, size_t c, void* ptr) {
  (ContextDelegateHolder:ptr).call(a, b, c);
}

(cl_context, cl_int) createContextFromType(cl_context_properties[] props, cl_device_type type, void delegate(char* errinfo, void* private_info, size_t cb) notify) {
  cl_int ret;
  auto hdr = new ContextDelegateHolder;
  hdr.dg = notify;
  props ~= cl_context_properties:0;
  auto res = clCreateContextFromType(props.ptr, type, &callHolder, void*:hdr, &ret);
  return (res, ret);
}

alias openclSource = [
  "__kernel void VectorAdd(__global int* c, __global int* a, __global int* b)\n"[],
  "{\n"[],
  "               // Index of the elements to add\n"[],
  "               unsigned int n = get_global_id(0);\n"[],
  "               // Sum the n’th element of vectors a and b and store in c\n"[],
  "               c[n] = a[n] + b[n];\n"[],
  "}\n"[]
];

alias initialData1 = [37, 50, 54, 50, 56,0, 79, 112, 101, 110, 67, 76, 32, 43, 56, 100, 50, 25, 15, 17];
alias InitialData2 = [35, 51, 54, 58, 55,32, 0, 0, 0, 0, 0, 0, 0, 44, 55, 14, 58, 75, 18, 15];
 
alias size = 2048;
 
void main() {
  int ids;
  clGetPlatformIDs(0, cl_platform_id*:null, &ids);
  auto platforms = new cl_platform_id[ids];
  clGetPlatformIDs(ids, platforms.ptr, cl_uint*:null);
  writeln "$ids platform(s). ";
  int i; cl_platform_id platform;
  cl_device_id[] getDevices(cl_platform_id platform) {
    int devs;
    clGetDeviceIDs (platform, CL_DEVICE_TYPE_ALL, 0, cl_device_id*:null, &devs);
    if (!devs) return null;
    auto devlist = new cl_device_id[devs];
    clGetDeviceIDs (platform, CL_DEVICE_TYPE_ALL, devs, devlist.ptr, int*:null);
    return devlist;
  }
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
    auto devlist = getDevices(platform);
    onExit devlist.free;
    if (!devlist.length) {
      writeln "No devices. ";
    } else {
      int k; cl_device_id dev;
      string devinfo; int enum2;
      while ((k, dev), (devinfo, enum2)) <- cross (
        [for k <- 0..devlist.length: (k, devlist[k])],
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
  platform = platforms[0];
  int device = 0;
  cl_context_properties[] props;
  props ~= CL_CONTEXT_PLATFORM;
  props ~= cl_context_properties: platform;
  auto ctx = createContextFromType(props, CL_DEVICE_TYPE_ALL, null);
  writeln "ctx res is $ctx";
  auto dev = getDevices(platform)[device];
  auto queue = clCreateCommandQueue(ctx[0], dev, 0, null);
  writeln "Command queue created. ";
}
