typedef unsigned char byte;
void stamp_ptr(int *srcp, int *dstp, int w) {
  for (int x = 0; x < w; ++x) {
    int src = *srcp;
    int srcalpha = ((byte*)&src)[3], dstalpha = ((byte*)dstp)[3], srcalpha2 = 255 - srcalpha;
    int dst = ((dstalpha + (((255 - dstalpha) * srcalpha) >> 8)) << 24)
          | ((((byte*)&src)[0] * srcalpha + ((byte*)dstp)[0] * srcalpha2) >> 8)
          | ((((byte*)&src)[1] * srcalpha + ((byte*)dstp)[1] * srcalpha2) & 0xff00)
          | (((((byte*)&src)[2] * srcalpha + ((byte*)dstp)[2] * srcalpha2) >> 8) << 16);
    *dstp = dst;
    srcp ++;
    dstp ++;
  }
}
