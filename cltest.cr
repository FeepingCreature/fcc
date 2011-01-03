module cltest;

c_include "CL/cl.h";
import sys, std.string;

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

void clCheckRes (int i) {
  if (i != 0) {
    writeln "Failed with $i! ";
    _interrupt 3;
  }
}

template clCheckCall(alias A) <<EOF
  template clCheckCall(T) <<EO2
    type-of A(init!T, null) clCheckCall(T t) {
      int error;
      onExit clCheckRes (error);
      return A(t, &error);
    }
  EO2
EOF

cl_context createContextFromType(cl_context_properties[] props, cl_device_type type, void delegate(char* errinfo, void* private_info, size_t cb) notify) {
  cl_int ret;
  auto tup = dgwrapper!(char*, void*, size_t)(notify);
  props ~= cl_context_properties:0;
  return clCheckCall!clCreateContextFromType (props.ptr, type, tup);
}

import sdl;

int main() {
  auto openclSource = "
  __kernel void mandel(__global int* res, int2 size, int iters, float4 rect) {
      float blend = 0;
      int aa = 4;
      int ix = get_global_id(0), iy = get_global_id(1);
      for (int sy = 0; sy < aa; sy++) {
        for (int sx = 0; sx < aa; sx++) {
          float x = ix + (float) sx / aa, y = iy + (float) sy / aa;
          float2 c = (float2) (x, y) / (float2) (size.x, size.y);
          float2 rectsize = rect.zw - rect.xy;
          c = rect.xy + c * rectsize;
          float2 z = c;
          int i;
          for (i = 0; i < iters; ++i) {
            float2 p = z * z;
            if (p.x + p.y > 4) break;
            z = (float2) (p.x - p.y, 2 * z.x * z.y) + c;
          }
          blend += i;
        }
      }
      res[iy * size.x + ix] = (int) (blend / (aa * aa));
    }"[];
  int ids;
  clCheckRes clGetPlatformIDs(0, null, &ids);
  auto platforms = new cl_platform_id[ids];
  clCheckRes clGetPlatformIDs(ids, platforms.ptr, null);
  writeln "$ids platform(s). ";
  cl_device_id[] getDevices(cl_platform_id platform) {
    int devs;
    clCheckRes clGetDeviceIDs (platform, CL_DEVICE_TYPE_ALL, 0, null, &devs);
    if (!devs) return null;
    auto devlist = new cl_device_id[devs];
    clCheckRes clGetDeviceIDs (platform, CL_DEVICE_TYPE_ALL, devs, devlist.ptr, null);
    return devlist;
  }
  while (int i, cl_platform_id platform) <- [for k <- 0..ids: (k, platforms[k])] {
    while (string info, int enum) <- [
     ("Profile"[], CL_PLATFORM_PROFILE),
     ("Version"[], CL_PLATFORM_VERSION),
     ("Name"[],    CL_PLATFORM_NAME),
     ("Vendor"[],  CL_PLATFORM_VENDOR),
     ("Extensions"[], CL_PLATFORM_EXTENSIONS)]
    {
      int size;
      clCheckRes clGetPlatformInfo (platform, enum, 0, null, &size);
      auto store = new char[size];
      onExit store.free();
      clCheckRes clGetPlatformInfo (platform, enum, size, store.ptr, int*:null);
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
        clCheckRes clGetDeviceInfo (dev, enum2, 0, null, &size);
        auto devstore = new char[size];
        onExit devstore.free;
        clCheckRes clGetDeviceInfo (dev, enum2, size, devstore.ptr, int*:null);
        writeln "  $k: $devinfo = $devstore ($size)";
      }
    }
  }
  auto platform = platforms[0];
  int device = 0;
  cl_context_properties[] props;
  props ~= CL_CONTEXT_PLATFORM;
  props ~= cl_context_properties: platform;
  auto ctx = createContextFromType(props, CL_DEVICE_TYPE_ALL, null);
  onExit clReleaseContext (ctx);
  writeln "Context created. ";
  auto dev = getDevices(platform)[device];
  auto queue = clCheckCall!clCreateCommandQueue (ctx, dev, 0);
  writeln "Command queue created. ";
  
  auto rect = vec4f(-2, -2, 2, 2);
  auto iters = cl_int:512, size = (cl_int:800, cl_int:600), output = new int[size[0]*size[1]];
  
  auto outvec = clCheckCall!clCreateBuffer (ctx, CL_MEM_WRITE_ONLY,
    (size-of int) * size[0] * size[1], null);
  onExit clReleaseMemObject (outvec);
  
  writeln "Buffers created. ";
  auto sourcelines = [for line <- splitAt("\n", iterOnce openclSource): line ~ "\n\x00"].eval[];
  writeln "$(sourcelines.length) lines of source. ";
  auto prog = clCreateProgramWithSource(ctx, sourcelines.length,
    [for line <- sourcelines: line.ptr].eval.ptr, null, null);
  onExit clReleaseProgram (prog);
  writeln "Building. ";
  {
    if auto err = clBuildProgram (prog, 0, null x 4) {
      int len;
      clGetProgramBuildInfo (prog, dev, CL_PROGRAM_BUILD_LOG, 0, null, &len);
      auto str = new char[len];
      clGetProgramBuildInfo (prog, dev, CL_PROGRAM_BUILD_LOG, len, str.ptr, null);
      writeln "Failed to build: $str";
      _interrupt 3;
    }
  }
  writeln "Program built. ";
  auto addKernel = clCheckCall!clCreateKernel (prog, "mandel".ptr);
  onExit clReleaseKernel (addKernel);
  
  writeln "Kernel created. ";
  
  void calc() {
    clCheckRes clSetKernelArg (addKernel, 0, size-of type-of outvec, void*:&outvec);
    clCheckRes clSetKernelArg (addKernel, 1, size-of type-of size, void*:&size);
    clCheckRes clSetKernelArg (addKernel, 2, size-of int, void*:&iters);
    clCheckRes clSetKernelArg (addKernel, 3, size-of type-of rect, void*:&rect);
    
    int[2] workSize = [size[0], size[1]];
    clCheckRes clEnqueueNDRangeKernel (queue, addKernel, 2, null, workSize.ptr, null, 0, null, null);
    // read-back
    clCheckRes clEnqueueReadBuffer (queue, outvec, CL_TRUE, 0, (size-of int) * size[0] * size[1], output.ptr, 0, null, null);
  }
  SDL_Init(32); // video
  auto surface = SDL_Surface*: SDL_SetVideoMode(size, 0, SDL_ANYFORMAT);
  bool update() {
    SDL_Flip(surface);
    SDL_Event ev;
    while SDL_PollEvent(&ev) {
      if ev.type == SDL_KEYDOWN {
        auto sym = (*(SDL_KeyboardEvent*:&ev)).keysym.sym;
        using rect {
              if (sym == 273) { auto dist = (w - y) * 0.1; y -= dist; w -= dist; }
          else if (sym == 274) { auto dist = (w - y) * 0.1; y += dist; w += dist; }
          else if (sym == 275) { auto dist = (z - x) * 0.1; x += dist; z += dist; }
          else if (sym == 276) { auto dist = (z - x) * 0.1; x -= dist; z -= dist; }
          else if (sym == 43) { auto dist = zw - xy, half = 0.5 * (xy + zw); dist *= 0.8; (x,y) = half - dist * 0.5; (z,w) = half + dist * 0.5; }
          else if (sym == 45) { auto dist = zw - xy, half = 0.5 * (xy + zw); dist /= 0.8; (x,y) = half - dist * 0.5; (z,w) = half + dist * 0.5; }
          else writeln "Key $(int:sym)";
        }
      }
      if ev.type == SDL_QUIT return true; // QUIT
    }
    return false;
  }
  void draw() {
    int factor1 = 255, factor2 = 256 * 255, factor3 = 256 * 256 * 255;
    auto f1f = float:factor1, f2f = float:factor2, f3f = float:factor3;
    for (int y = 0; y < size[1]; y++) {
      auto p = &((int*:surface.pixels)[y * int:surface.w]);
      for (int x = 0; x < size[0]; x++) {
        auto f = vec3f(output[y * size[0] + x] / 512.0);
        *(p++) = int:(f1f * f[2]) + int:(f2f * f[1]) & factor2 + int:(f3f * f[0]) & factor3;
      }
    }
  }
  while !update() { calc(); draw(); }
  return 0;
}
