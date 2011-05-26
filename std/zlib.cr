module std.zlib;

import c.zlib;

pragma(lib, "z");

class Deflate {
  z_stream stream;
  void init() {
    auto ret = deflateInit_(&stream, 6, ZLIB_VERSION, size-of z_stream);
    if ret != Z_OK raise-error new Error "ZLIB init error $ret (version '$ZLIB_VERSION')";
  }
  void fini() {
    auto ret = deflateEnd(&stream);
    if ret != Z_OK raise-error new Error "ZLIB fini error $ret (version '$ZLIB_VERSION')";
  }
  byte[] deflate(byte[] data) {
    byte[auto~] res;
    byte x 1024 buffer = void;
    stream.(avail_in, next_in) = (data.length, char*:data.ptr);
    do {
      stream.(avail_out, next_out) = (buffer.length, char*:buffer.ptr);
      // stream.(avail_out, next_out) = (buffer.length, char*:buffer.ptr);
      auto ret = .deflate(&stream, Z_FINISH);
      if ret == Z_STREAM_ERROR raise-error new Error "ZLIB deflate error $ret";
      int got = buffer.length - stream.avail_out;
      res ~= buffer[0..got];
    } while (stream.avail_in) { }
    return res[];
  }
}
