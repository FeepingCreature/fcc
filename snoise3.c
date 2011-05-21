#include "xmmintrin.h"
#include "emmintrin.h"
#include "stdio.h"

typedef float v4sf __attribute__ ((vector_size (16)));
typedef int v4si __attribute__ ((vector_size (16)));

__thread int setupPerm;

__thread int offsets[8][2][4];

__thread unsigned char *perm, *mperm; // perm mod 12

#define LET(A, B) typeof(B) A = B

#define vec4f(A, B, C, D) ((v4sf) _mm_set_ps(D, C, B, A))

#define vec1_4f(S) ((v4sf) _mm_set1_ps(S))

#define isum(V) ({ int i[4]; *(typeof(V)*) &i = V; i[0] + i[1] + i[2]; })

#define sum3(V) ({ float f[4]; *(typeof(V)*) &f = V; f[0] + f[1] + f[2]; })
#define sum4(V) ({ float f[4]; *(typeof(V)*) &f = V; f[0] + f[1] + f[2] + f[3]; })

void permsetup(void) {
  setupPerm = 1;
  int i, k, l;
  
  perm = malloc(sizeof(unsigned char) * 256);
  mperm = malloc(sizeof(unsigned char) * 256);
  
  {
    unsigned char permfill[256] = {162, 43, 153, 52, 83, 210, 193, 75, 227, 195, 233, 76, 83, 48, 252, 181, 101, 31, 13, 32, 38, 23, 72, 101, 100, 145, 105, 218, 135, 89, 39, 100, 162, 196, 51, 18, 185, 138, 76, 83, 228, 229, 128, 101, 76, 111, 68, 227, 114, 123, 72, 98, 219, 161, 8, 86, 212, 50, 219, 166, 139, 195, 195, 128, 74, 250, 154, 110, 150, 175, 36, 25, 96, 123, 101, 12, 236, 158, 227, 199, 77, 156, 6, 159, 203, 92, 27, 60, 155, 218, 239, 156, 184, 90, 213, 115, 38, 18, 39, 102, 191, 87, 177, 47, 64, 28, 224, 252, 176, 9, 111, 208, 112, 50, 78, 123, 243, 248, 99, 112, 52, 142, 253, 93, 30, 111, 56, 104, 217, 3, 204, 188, 144, 143, 155, 228, 55, 249, 45, 9, 152, 26, 250, 2, 135, 30, 4, 169, 30, 208, 56, 255, 15, 123, 237, 170, 17, 71, 182, 203, 246, 162, 184, 164, 103, 77, 49, 174, 186, 159, 201, 216, 41, 92, 246, 158, 112, 79, 99, 101, 231, 46, 88, 81, 94, 23, 24, 103, 43, 224, 151, 173, 217, 142, 64, 78, 203, 110, 151, 49, 22, 107, 3, 44, 110, 151, 253, 142, 125, 247, 3, 239, 42, 23, 238, 102, 114, 104, 58, 227, 164, 31, 214, 84, 98, 159, 67, 181, 19, 144, 133, 213, 19, 122, 245, 42, 217, 205, 0, 87, 104, 122, 35, 238, 96, 93, 116, 177, 56, 201, 147, 156, 229, 219, 16, 128};
    for (i = 0; i < 256; ++i) {
        perm[i] = permfill[i];
        mperm[i] = perm[i] % 12;
    }
  }
  
  static int offs_init[8][2][4]
    = {
      {{1, 0, 0, 0}, {1, 1, 0, 0}},
      {{0, 1, 0, 0}, {1, 1, 0, 0}},
      {{0, 0, 0, 0}, {0, 0, 0, 0}},
      {{0, 1, 0, 0}, {0, 1, 1, 0}},
      {{1, 0, 0, 0}, {1, 0, 1, 0}},
      {{0, 0, 0, 0}, {0, 0, 0, 0}},
      {{0, 0, 1, 0}, {1, 0, 1, 0}},
      {{0, 0, 1, 0}, {0, 1, 1, 0}}
    };
  for (i = 0; i < 8; ++i)
    for (k = 0; k < 2; ++k)
      for (l = 0; l < 4; ++l)
        offsets[i][k][l] = offs_init[i][k][l];
}

float noise3(float x, float y, float z) __attribute__ ((force_align_arg_pointer));
float noise3(float x, float y, float z) {
  v4sf vs[4], vsum;
  int gi[4], mask, c;
  v4sf v0;
  if (!setupPerm) permsetup();
  v4sf v = vec4f(x, y, z, 0);
  v4si indices;
  
  vsum = v + vec1_4f(sum3(v) / 3);
  indices = __builtin_ia32_psubd128 (__builtin_ia32_cvttps2dq(vsum), __builtin_ia32_psrldi128 ((v4si) vsum, 31));
  vs[0] = v - __builtin_ia32_cvtdq2ps(indices) + vec1_4f(isum(indices) / 6.0f);
  vs[1] = vs[0] + vec1_4f(     1.0f/6.0f);
  vs[2] = vs[0] + vec1_4f(     2.0f/6.0f);
  vs[3] = vs[0] + vec1_4f(-1.0f + 3.0f/6.0f);
  v4sf xxy = __builtin_ia32_shufps(vs[0], vs[0], _MM_SHUFFLE(0, 1, 0, 0));
  v4sf yzz = __builtin_ia32_shufps(vs[0], vs[0], _MM_SHUFFLE(0, 2, 2, 1));
  mask = __builtin_ia32_movmskps(__builtin_ia32_cmpltps(xxy, yzz));
  LET(opp, &offsets[mask & 7]);
  #define op (*opp)
  #define offs1 (op[0])
  #define offs2 (op[1])
  vs[1] -= __builtin_ia32_cvtdq2ps(*(v4si*)&offs1);
  vs[2] -= __builtin_ia32_cvtdq2ps(*(v4si*)&offs2);
  int indexfield[4]; *(typeof(indices)*) indexfield = indices;
  #define ii indexfield[0]
  #define jj indexfield[1]
  #define kk indexfield[2]
  #define i1 offs1[0]
  #define i2 offs2[0]
  #define j1 offs1[1]
  #define j2 offs2[1]
  #define k1 offs1[2]
  #define k2 offs2[2]
  gi[0] = mperm[(perm[(perm[(kk   )&0xff]+jj   )&0xff]+ii   )&0xff];
  gi[1] = mperm[(perm[(perm[(kk+k1)&0xff]+jj+j1)&0xff]+ii+i1)&0xff];
  gi[2] = mperm[(perm[(perm[(kk+k2)&0xff]+jj+j2)&0xff]+ii+i2)&0xff];
  gi[3] = mperm[(perm[(perm[(kk+1 )&0xff]+jj+1 )&0xff]+ii+1 )&0xff];
  float factors[4];
  float pair[3], res[4];
  pair[0] = 1; pair[1] = -1; pair[2] = -1;
  for (c = 0; c < 4; ++c) {
    LET(vscp, &(vs[c]));
    LET(current, *vscp);
    {
      LET(A, current * current);
      LET(B, __builtin_ia32_shufps(A, A, _MM_SHUFFLE(1, 1, 1, 1)));
      LET(C, __builtin_ia32_shufps(A, A, _MM_SHUFFLE(2, 2, 2, 2)));
      LET(D, A + B + C);
      LET(E, vec1_4f(0.6f) - D);
      factors[c] = *(float*) &E;
    }
    if (factors[c] >= 0) {
      int id = gi[c];
      res[c] = (((float*)vscp)[id >> 3] * pair[id & 1]) + (((float*)vscp)[(((id >> 2) | (id >> 3)) & 1) + 1] * pair[id&2]);
    } else {
      factors[c] = 0;
      res[c] = 0;
    }
  }
  v4sf vfactors = vec4f(factors[0], factors[1], factors[2], factors[3]);
  vfactors *= vfactors;
  vfactors *= vfactors;
  v4sf vres = vec4f(res[0], res[1], res[2], res[3]);
  vres *= vfactors;
  return 0.5f + 16 * sum4(vres);
}
