module cltest;

c_include "CL/cl.h";
import sys;

extern(C) cl_context clCreateContextFromType(
  cl_context_properties *properties,
  cl_device_type device_type,
  void function(char* errinfo, void* private_info, size_t cb, void* user_data) pfn_notify,
  void* user_data, cl_int* errcode_ret);
extern(C) cl_int clBuildProgram(
  cl_program, cl_uint, cl_device_id*, char*,
  void function(cl_program, void*), void*);

template dgwrapper(T) <<EOF
  class DelegateHolder {
    void delegate(T) dg;
    void call(T t) { dg(t); }
  }
  void callHolder(T t, void* ptr) {
    (DelegateHolder:ptr).call(t);
  }
  (void function(T, void*), void*) dgwrapper(void delegate(T) dg) {
    auto res = new DelegateHolder;
    res.dg = dg;
    return (&callHolder, void*:res);
  }
EOF

void check_res (int i) {
  if (i != 0) {
    writeln "Failed with $i! ";
    _interrupt 3;
  }
}

template clCheckCall(alias A) <<EOF
  template clCheckCall(T) <<EO2
    typeof(A(init!T, null)) clCheckCall(T t) {
      int error;
      onExit check_res (error);
      return A(t, &error);
    }
  EO2
EOF

cl_context createContextFromType(cl_context_properties[] props, cl_device_type type, void delegate(char* errinfo, void* private_info, size_t cb) notify) {
  cl_int ret;
  auto tup = dgwrapper!(char*, void*, size_t)(notify);
  props ~= cl_context_properties:0;
  auto res = clCheckCall!clCreateContextFromType (props.ptr, type, tup);
  return res;
}

int main() {
  auto openclSource = [
    "__kernel void VectorAdd(__global int* c, __global int* a, __global int* b)\n"[],
    "{\n"[],
    "               // Index of the elements to add\n"[],
    "               unsigned int n = get_global_id(0);\n"[],
    "               // Sum the n’th element of vectors a and b and store in c\n"[],
    "               c[n] = a[n] + b[n];\n"[],
    "}\n"[]
  ];
  auto initialData1 = [37, 50, 54, 50, 56, 0, 79, 112, 101, 110, 67, 76, 32, 43, 56, 100, 50, 25, 15, 17];
  auto initialData2 = [35, 51, 54, 58, 55, 32, 0,   0,   0,   0,  0,  0,  0, 44, 55,  14, 58, 75, 18, 15];
  int[] data1, data2;
  alias SIZE = 2048;
  while (data1.length < SIZE) data1 ~= initialData1;
  data1 = data1[0 .. SIZE];
  while (data2.length < SIZE) data2 ~= initialData2;
  data2 = data2[0 .. SIZE];
  
  int ids;
  check_res clGetPlatformIDs(0, null, &ids);
  auto platforms = new cl_platform_id[ids];
  check_res clGetPlatformIDs(ids, platforms.ptr, null);
  writeln "$ids platform(s). ";
  int i; cl_platform_id platform;
  cl_device_id[] getDevices(cl_platform_id platform) {
    int devs;
    check_res clGetDeviceIDs (platform, CL_DEVICE_TYPE_ALL, 0, null, &devs);
    if (!devs) return null;
    auto devlist = new cl_device_id[devs];
    check_res clGetDeviceIDs (platform, CL_DEVICE_TYPE_ALL, devs, devlist.ptr, null);
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
      check_res clGetPlatformInfo (platform, enum, 0, null, &size);
      auto store = new char[size];
      onExit store.free();
      check_res clGetPlatformInfo (platform, enum, size, store.ptr, int*:null);
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
        check_res clGetDeviceInfo (dev, enum2, 0, null, &size);
        auto devstore = new char[size];
        onExit devstore.free;
        check_res clGetDeviceInfo (dev, enum2, size, devstore.ptr, int*:null);
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
  onExit clReleaseContext (ctx);
  writeln "Context created. ";
  auto dev = getDevices(platform)[device];
  int error;
  auto queue = clCreateCommandQueue(ctx, dev, 0, &error);
  check_res error;
  writeln "Command queue created. ";
  auto gpuvec1 = clCreateBuffer(ctx, CL_MEM_READ_ONLY | CL_MEM_COPY_HOST_PTR,
    int.sizeof * SIZE, data1.ptr, &error);
  check_res error;
  onExit clReleaseMemObject (gpuvec1);
  auto gpuvec2 = clCreateBuffer(ctx, CL_MEM_READ_ONLY | CL_MEM_COPY_HOST_PTR,
    int.sizeof * SIZE, data2.ptr, &error);
  check_res error;
  onExit clReleaseMemObject (gpuvec2);
  auto outvec = clCreateBuffer(ctx, CL_MEM_WRITE_ONLY,
    int.sizeof * SIZE, null, &error);
  onExit clReleaseMemObject (outvec);
  check_res error;
  writeln "Buffers created. ";
  auto prog = clCreateProgramWithSource(ctx, openclSource.length,
    [for line <- openclSource: line.ptr].eval.ptr, null, null);
  onExit clReleaseProgram (prog);
  check_res clBuildProgram (prog, 0, null x 4);
  writeln "Program built. ";
  auto addKernel = clCreateKernel(prog, "VectorAdd", &error);
  onExit clReleaseKernel (addKernel);
  check_res error;
  writeln "Kernel created. ";
  check_res clSetKernelArg (addKernel, 0, typeof(outvec).sizeof, void*:&outvec);
  check_res clSetKernelArg (addKernel, 1, typeof(gpuvec1).sizeof, void*:&gpuvec1);
  check_res clSetKernelArg (addKernel, 2, typeof(gpuvec2).sizeof, void*:&gpuvec2);
  writeln "Args set. ";
  int[1] workSize = [SIZE];
  check_res clEnqueueNDRangeKernel (queue, addKernel, 1, null, workSize.ptr, null, 0, null, null);
  writeln "Task queued. ";
  // read-back
  auto output = new int[SIZE];
  check_res clEnqueueReadBuffer (queue, outvec, CL_TRUE, 0, int.sizeof * SIZE, output.ptr, 0, null, null);
  writeln "Read back. ";
  int rows, c;
  while rows <- 0..(SIZE/20) {
    while c <- 0..20 {
      printf ("%c", output[rows * 20 + c]);
    }
    printf "\n";
  }
  return 0;
}
