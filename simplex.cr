module simplex;

int[] perm, mperm; // perm mod 12
vec3i x 12 grad3;

bool setupPerm;

float dot2(int x 4 whee, float a, float b) {
  return whee[0] * a + whee[1] * b;
}

class KISS {
  int x, y, z, w, carry, k, m;
  void init() { (x, y, z, w, carry) = (1, 2, 4, 8, 0); }
  void seed(int i) {
    (x, y, z, w) = (i | 1, i | 2, i | 4, i | 8);
    carry = 0;
  }
  int rand() {
    x = x * 69069 + 1;
    y xor= y << 13;
    y xor= y >> 17;
    y xor= y << 5;
    k = (z >> 2) + (w >> 3) + (carry >> 2);
    m = w + w + z + carry;
    z = w;
    w = m;
    carry = k >> 30;
    return x + y + w;
  }
}

vec3i x 2[] offsets;

void permsetup() {
  setupPerm = true;
  (perm, mperm) = (new int[] 256) x 2;
  int seed = 34;
  auto gen = new KISS;
  gen.seed(seed);
  int x 256 firstPerm;
  for int i <- 0..256 {
    perm[i] = (gen.rand() & 0x7fff_ffff) % 256;
    mperm[i] = perm[i] % 12;
  }
  int i;
  alias values = [1, 1, 0,
                 -1, 1, 0,
                  1,-1, 0,
                 -1,-1, 0,
                 
                  1, 0, 1,
                 -1, 0, 1,
                  1, 0,-1,
                 -1, 0,-1,
                 
                  0, 1, 1,
                  0,-1, 1,
                  0, 1,-1,
                  0,-1,-1];
  while ((int k, int l), int idx) <- zip (cross (0..12, 0..3), 0..-1) {
    grad3[k][l] = values[idx];
  }
  offsets = new vec3i x 2[] 8;
  offsets[0] = [vec3i.X, vec3i(1, 1, 0)];
  offsets[1] = [vec3i.Y, vec3i(1, 1, 0)];
  offsets[3] = [vec3i.Y, vec3i(0, 1, 1)];
  offsets[4] = [vec3i.X, vec3i(1, 0, 1)];
  offsets[6] = [vec3i.Z, vec3i(1, 0, 1)];
  offsets[7] = [vec3i.Z, vec3i(0, 1, 1)];
}

float noise2(vec2f f) {
  if !setupPerm permsetup;
  alias sqrt3 = sqrtf(3);
  alias f2 = 0.5 * (sqrt3 - 1);
  alias g2 = (3 - sqrt3) / 6;
  float x 3  n = void;
  
  float s = (f.x + f.y) * f2;
  int i = fastfloor(f.x + s), j = fastfloor(f.y + s);
  
  float t = (i + j) * g2;
  vec2f x 3  xy;
  xy[0] = f - (vec2i(i,j) - vec2f(t));
  
  int i1, j1;
  if xy[0].x > xy[0].y i1 = 1;
  else j1 = 1;
  
  {
    auto temp = 1 - 2 * g2;
    xy[1] = xy[0] - vec2i(i1, j1) + vec2f (g2);
    xy[2] = xy[0] - vec2f(temp);
  }
  int ii = i & 255, jj = j & 255;
  
  int x 3  gi = void;
  // gi[0] = mperm[(ii      + perm[jj     ]) & 255];
  // gi[1] = mperm[(ii + i1 + perm[jj + j1]) & 255];
  // gi[2] = mperm[(ii +  1 + perm[jj +  1]) & 255];
  gi[0] = mperm[jj * 256 + ii];
  gi[1] = mperm[(jj + j1) * 256 + (ii + i1)];
  gi[2] = mperm[(jj + 1) * 256 + (ii + 1)];
  
  for (int k = 0; k < 3; ++k) {
    float ft = 0.5 - xy[k].x*xy[k].x - xy[k].y*xy[k].y;
    if ft < 0 n[k] = 0;
    else {
      ft = ft * ft;
      n[k] = ft * ft * dot2(grad3[gi[k]], xy[k]);
    }
  }
  return 0.5 + 35 * (n[0] + n[1] + n[2]);
}

double sumval;
int count;

void time-it(string t, void delegate() dg) {
  // calibrate
  int from1, to1, from2, to2;
  from1 = rdtsc[1];
  delegate void() { } ();
  to1 = rdtsc[1];
  // measure
  from2 = rdtsc[1];
  dg();
  to2 = rdtsc[1];
  auto delta = (to2 - from2) - (to1 - from1);
  if !count sumval = 0;
  sumval += delta; count += 1;
  writeln "$t: $delta, average $(sumval / count)";
}

void testAlign(string name, void* p) {
  if !(int:p & 0b1111) writeln "$name: 16-aligned";
  else if !(int:p & 0b111) writeln "$name: 8-aligned";
  else if !(int:p & 0b11) writeln "$name: 4-aligned";
  else writeln "$name: not aligned";
}

struct NoiseContext {
  int x 4 x 2 x 8 offsets;
  byte* perm, mperm; // perm mod 12
}

__defConstant(".noise3_LC1", 1051372203);
__defConstant(".noise3_LC2", 1042983595);
__defConstant(".noise3_LC3", 3204448256, 3204448256, 3204448256, 3204448256);
__defConstant(".noise3_LC4", 1042983595, 1042983595, 1042983595, 1042983595);
__defConstant(".noise3_LC5", 1051372203, 1051372203, 1051372203, 1051372203);
__defConstant(".noise3_LC8", 1058642330, 1058642330, 1058642330, 1058642330);
__defConstant(".noise3_LC9", 1098907648);
__defConstant(".noise3_LC10", 1056964608);

// blatant cheating: compiled with gcc, then copypasted. see fcc:snoise3.c
extern(C) float noise3_asm(float x, float y, float z, NoiseContext* nc) {
  asm `fldz`;
  asm `andl $-16, %esp`;
  asm `pushl  %edi`;
  asm `pushl  %esi`;
  asm `pushl  %ebx`;
  asm `subl $244, %esp`;
  asm `movl 20(%ebp), %ebx`;
  asm `movss  16(%ebp), %xmm1`;
  asm `movss  12(%ebp), %xmm0`;
  asm `movss  8(%ebp), %xmm2`;
  asm `unpcklps %xmm0, %xmm2`;
  asm `movaps %xmm2, %xmm0`;
  asm `movlhps  %xmm1, %xmm0`;
  asm `movaps %xmm0, 128(%esp)`;
  asm `flds 132(%esp)`;
  asm `fadds  128(%esp)`;
  asm `fadds  136(%esp)`;
  asm `fmuls  .noise3_LC1`;
  asm `fstps  12(%esp)`;
  asm `movss  12(%esp), %xmm3`;
  asm `shufps $0, %xmm3, %xmm3`;
  asm `movaps %xmm3, %xmm1`;
  asm `addps  %xmm0, %xmm1`;
  asm `movdqa %xmm1, %xmm2`;
  asm `cvttps2dq  %xmm1, %xmm1`;
  asm `psrld  $31, %xmm2`;
  asm `psubd  %xmm2, %xmm1`;
  asm `movdqa %xmm1, 32(%esp)`;
  asm `cvtdq2ps %xmm1, %xmm1`;
  asm `movdqa 32(%esp), %xmm2`;
  asm `movl 32(%esp), %eax`;
  asm `movdqa %xmm2, 192(%esp)`;
  asm `subps  %xmm1, %xmm0`;
  asm `addl 196(%esp), %eax`;
  asm `movaps .noise3_LC3, %xmm1`;
  asm `addl 200(%esp), %eax`;
  asm `movl %eax, 60(%esp)`;
  asm `fildl  60(%esp)`;
  asm `fmuls  .noise3_LC2`;
  asm `fstps  12(%esp)`;
  asm `movss  12(%esp), %xmm3`;
  asm `shufps $0, %xmm3, %xmm3`;
  asm `addps  %xmm3, %xmm0`;
  asm `addps  %xmm0, %xmm1`;
  asm `movaps %xmm0, 64(%esp)`;
  asm `movaps %xmm1, 112(%esp)`;
  asm `movaps %xmm0, %xmm2`;
  asm `movaps %xmm0, %xmm1`;
  asm `shufps $41, %xmm0, %xmm2`;
  asm `shufps $16, %xmm0, %xmm1`;
  asm `cmpltps  %xmm2, %xmm1`;
  asm `movmskps %xmm1, %edx`;
  asm `movaps .noise3_LC4, %xmm1`;
  asm `andl $7, %edx`;
  asm `addps  %xmm0, %xmm1`;
  asm `sall $5, %edx`;
  asm `leal (%ebx,%edx), %edx`;
  asm `movups (%edx), %xmm2`;
  asm `cvtdq2ps %xmm2, %xmm2`;
  // asm `cvtdq2ps (%edx), %xmm2`;
  asm `subps  %xmm2, %xmm1`;
  asm `movups 16(%edx), %xmm2`;
  asm `cvtdq2ps %xmm2, %xmm2`;
  // asm `cvtdq2ps 16(%edx), %xmm2`;
  asm `movaps %xmm1, 80(%esp)`;
  asm `movaps .noise3_LC5, %xmm1`;
  asm `addps  %xmm0, %xmm1`;
  asm `mulps  %xmm0, %xmm0`;
  asm `subps  %xmm2, %xmm1`;
  asm `movaps %xmm0, %xmm2`;
  asm `movaps %xmm1, 96(%esp)`;
  asm `shufps $170, %xmm0, %xmm2`;
  asm `movdqa 32(%esp), %xmm1`;
  asm `movl 260(%ebx), %eax`;
  asm `movdqa %xmm1, 176(%esp)`;
  asm `movl %eax, 32(%esp)`;
  asm `movzbl 184(%esp), %esi`;
  asm `movl 256(%ebx), %eax`;
  asm `movl 184(%esp), %edi`;
  asm `movzbl (%eax,%esi), %ecx`;
  asm `movzbl 180(%esp), %ebx`;
  asm `movaps %xmm0, %xmm1`;
  asm `leal (%ecx,%ebx), %esi`;
  asm `shufps $85, %xmm0, %xmm1`;
  asm `andl $255, %esi`;
  asm `movzbl 176(%esp), %ebx`;
  asm `movzbl (%eax,%esi), %ecx`;
  asm `addps  %xmm0, %xmm1`;
  asm `leal (%ecx,%ebx), %esi`;
  asm `addps  %xmm2, %xmm1`;
  asm `movl 32(%esp), %ecx`;
  asm `andl $255, %esi`;
  asm `movl 176(%esp), %ebx`;
  asm `movzbl (%ecx,%esi), %esi`;
  asm `movl 180(%esp), %ecx`;
  asm `movl %esi, 208(%esp)`;
  asm `addl (%edx), %ebx`;
  asm `addl 4(%edx), %ecx`;
  asm `movl %ebx, 28(%esp)`;
  asm `addl 8(%edx), %edi`;
  asm `andl $255, %edi`;
  asm `movzbl (%eax,%edi), %ebx`;
  asm `leal (%ebx,%ecx), %edi`;
  asm `movzbl 28(%esp), %ebx`;
  asm `andl $255, %edi`;
  asm `movzbl (%eax,%edi), %ecx`;
  asm `leal (%ecx,%ebx), %edi`;
  asm `movl 32(%esp), %ecx`;
  asm `andl $255, %edi`;
  asm `movl 176(%esp), %ebx`;
  asm `movzbl (%ecx,%edi), %edi`;
  asm `movl %edi, 212(%esp)`;
  asm `movl 180(%esp), %edi`;
  asm `addl 16(%edx), %ebx`;
  asm `addl 20(%edx), %edi`;
  asm `movl 24(%edx), %edx`;
  asm `addl 184(%esp), %edx`;
  asm `andl $255, %edx`;
  asm `movzbl (%eax,%edx), %edx`;
  asm `addl %edi, %edx`;
  asm `movzbl %dl, %edx`;
  asm `movzbl (%eax,%edx), %edx`;
  asm `addl %ebx, %edx`;
  asm `movzbl %dl, %edx`;
  asm `movzbl (%ecx,%edx), %edx`;
  asm `movl %edx, 216(%esp)`;
  asm `movl 184(%esp), %ebx`;
  asm `movaps .noise3_LC8, %xmm2`;
  asm `incl %ebx`;
  asm `movaps %xmm2, %xmm0`;
  asm `andl $255, %ebx`;
  asm `subps  %xmm1, %xmm0`;
  asm `movzbl (%eax,%ebx), %edx`;
  asm `movl 180(%esp), %ebx`;
  asm `leal 1(%ebx,%edx), %edx`;
  asm `andl $255, %edx`;
  asm `movzbl (%eax,%edx), %eax`;
  asm `movl 176(%esp), %edx`;
  asm `leal 1(%edx,%eax), %eax`;
  asm `andl $255, %eax`;
  asm `movzbl (%ecx,%eax), %eax`;
  asm `movss  %xmm0, 12(%esp)`;
  asm `movl %eax, 220(%esp)`;
  asm `flds 12(%esp)`;
  asm `movl $0x3f800000, 228(%esp)`;
  asm `fsts 160(%esp)`;
  asm `movl $0xbf800000, 232(%esp)`;
  asm `movl $0xbf800000, 236(%esp)`;
  asm `fcomip %st(1), %st`;
  asm `jb .noise3_L14`;
  asm `fstp %st(0)`;
  asm `movl %esi, %edx`;
  asm `movl %esi, %eax`;
  asm `sarl $3, %edx`;
  asm `movl %esi, %ecx`;
  asm `sarl $2, %eax`;
  asm `andl $2, %ecx`;
  asm `orl  %edx, %eax`;
  asm `andl $1, %esi`;
  asm `andl $1, %eax`;
  asm `incl %eax`;
  asm `flds 64(%esp,%eax,4)`;
  asm `fmuls  228(%esp,%ecx,4)`;
  asm `flds 64(%esp,%edx,4)`;
  asm `fmuls  228(%esp,%esi,4)`;
  asm `faddp  %st, %st(1)`;
  asm `fstps  144(%esp)`;
  asm `.noise3_L3:`;
  asm `movaps 80(%esp), %xmm0`;
  asm `mulps  %xmm0, %xmm0`;
  asm `movaps %xmm0, %xmm1`;
  asm `movaps %xmm0, %xmm3`;
  asm `shufps $85, %xmm0, %xmm1`;
  asm `shufps $170, %xmm0, %xmm3`;
  asm `addps  %xmm0, %xmm1`;
  asm `movaps %xmm2, %xmm0`;
  asm `addps  %xmm3, %xmm1`;
  asm `subps  %xmm1, %xmm0`;
  asm `movss  %xmm0, 12(%esp)`;
  asm `flds 12(%esp)`;
  asm `fsts 164(%esp)`;
  asm `fldz`;
  asm `fxch %st(1)`;
  asm `fcomip %st(1), %st`;
  asm `jb .noise3_L15`;
  asm `fstp %st(0)`;
  asm `movl 212(%esp), %edx`;
  asm `movl %edx, %ecx`;
  asm `movl %edx, %eax`;
  asm `sarl $3, %ecx`;
  asm `movl %edx, %ebx`;
  asm `sarl $2, %eax`;
  asm `andl $2, %ebx`;
  asm `orl  %ecx, %eax`;
  asm `andl $1, %edx`;
  asm `andl $1, %eax`;
  asm `incl %eax`;
  asm `flds 80(%esp,%eax,4)`;
  asm `fmuls  228(%esp,%ebx,4)`;
  asm `flds 80(%esp,%ecx,4)`;
  asm `fmuls  228(%esp,%edx,4)`;
  asm `faddp  %st, %st(1)`;
  asm `fstps  148(%esp)`;
  asm `.noise3_L5:`;
  asm `movaps 96(%esp), %xmm0`;
  asm `mulps  %xmm0, %xmm0`;
  asm `movaps %xmm0, %xmm1`;
  asm `movaps %xmm0, %xmm3`;
  asm `shufps $85, %xmm0, %xmm1`;
  asm `shufps $170, %xmm0, %xmm3`;
  asm `addps  %xmm0, %xmm1`;
  asm `movaps %xmm2, %xmm0`;
  asm `addps  %xmm3, %xmm1`;
  asm `subps  %xmm1, %xmm0`;
  asm `movss  %xmm0, 12(%esp)`;
  asm `flds 12(%esp)`;
  asm `fsts 168(%esp)`;
  asm `fldz`;
  asm `fxch %st(1)`;
  asm `fcomip %st(1), %st`;
  asm `jb .noise3_L16`;
  asm `fstp %st(0)`;
  asm `movl 216(%esp), %edx`;
  asm `movl %edx, %ecx`;
  asm `movl %edx, %eax`;
  asm `sarl $3, %ecx`;
  asm `movl %edx, %ebx`;
  asm `sarl $2, %eax`;
  asm `andl $2, %ebx`;
  asm `orl  %ecx, %eax`;
  asm `andl $1, %edx`;
  asm `andl $1, %eax`;
  asm `incl %eax`;
  asm `flds 96(%esp,%eax,4)`;
  asm `fmuls  228(%esp,%ebx,4)`;
  asm `flds 96(%esp,%ecx,4)`;
  asm `fmuls  228(%esp,%edx,4)`;
  asm `faddp  %st, %st(1)`;
  asm `fstps  152(%esp)`;
  asm `.noise3_L7:`;
  asm `movaps 112(%esp), %xmm0`;
  asm `mulps  %xmm0, %xmm0`;
  asm `movaps %xmm0, %xmm1`;
  asm `movaps %xmm0, %xmm3`;
  asm `shufps $85, %xmm0, %xmm1`;
  asm `shufps $170, %xmm0, %xmm3`;
  asm `addps  %xmm0, %xmm1`;
  asm `addps  %xmm3, %xmm1`;
  asm `subps  %xmm1, %xmm2`;
  asm `movss  %xmm2, 12(%esp)`;
  asm `flds 12(%esp)`;
  asm `fsts 172(%esp)`;
  asm `fldz`;
  asm `fxch %st(1)`;
  asm `fcomip %st(1), %st`;
  asm `jb .noise3_L12`;
  asm `fstp %st(0)`;
  asm `movl 220(%esp), %edx`;
  asm `movl %edx, %ecx`;
  asm `movl %edx, %eax`;
  asm `sarl $3, %ecx`;
  asm `movl %edx, %ebx`;
  asm `sarl $2, %eax`;
  asm `andl $2, %ebx`;
  asm `orl  %ecx, %eax`;
  asm `andl $1, %edx`;
  asm `andl $1, %eax`;
  asm `incl %eax`;
  asm `flds 112(%esp,%eax,4)`;
  asm `fmuls  228(%esp,%ebx,4)`;
  asm `flds 112(%esp,%ecx,4)`;
  asm `fmuls  228(%esp,%edx,4)`;
  asm `faddp  %st, %st(1)`;
  asm `fstps  156(%esp)`;
  asm `.noise3_L10:`;
  asm `movss  172(%esp), %xmm1`;
  asm `movss  168(%esp), %xmm0`;
  asm `movss  160(%esp), %xmm2`;
  asm `movss  152(%esp), %xmm3`;
  asm `unpcklps %xmm1, %xmm0`;
  asm `movaps %xmm0, %xmm1`;
  asm `movss  164(%esp), %xmm0`;
  asm `unpcklps %xmm0, %xmm2`;
  asm `movaps %xmm2, %xmm0`;
  asm `movss  156(%esp), %xmm2`;
  asm `movlhps  %xmm1, %xmm0`;
  asm `unpcklps %xmm2, %xmm3`;
  asm `movss  148(%esp), %xmm1`;
  asm `movaps %xmm3, %xmm2`;
  asm `mulps  %xmm0, %xmm0`;
  asm `movss  144(%esp), %xmm3`;
  asm `mulps  %xmm0, %xmm0`;
  asm `unpcklps %xmm1, %xmm3`;
  asm `movaps %xmm3, %xmm1`;
  asm `movlhps  %xmm2, %xmm1`;
  asm `mulps  %xmm1, %xmm0`;
  asm `movaps %xmm0, 128(%esp)`;
  asm `flds 132(%esp)`;
  asm `fadds  128(%esp)`;
  asm `fadds  136(%esp)`;
  asm `fadds  140(%esp)`;
  asm `fmuls  .noise3_LC9`;
  asm `fadds  .noise3_LC10`;
  asm `addl $244, %esp`;
  asm `popl %ebx`;
  asm `popl %esi`;
  asm `popl %edi`;
  asm `leave`;
  asm `ret`;
  asm `.p2align 4,,10`;
  asm `.p2align 3`;
  asm `.noise3_L14:`;
  asm `fsts 160(%esp)`;
  asm `fstps  144(%esp)`;
  asm `jmp  .noise3_L3`;
  asm `.p2align 4,,10`;
  asm `.p2align 3`;
  asm `.noise3_L12:`;
  asm `fsts 172(%esp)`;
  asm `fstps  156(%esp)`;
  asm `jmp  .noise3_L10`;
  asm `.p2align 4,,10`;
  asm `.p2align 3`;
  asm `.noise3_L16:`;
  asm `fsts 168(%esp)`;
  asm `fstps  152(%esp)`;
  asm `jmp  .noise3_L7`;
  asm `.p2align 4,,10`;
  asm `.p2align 3`;
  asm `.noise3_L15:`;
  asm `fsts 164(%esp)`;
  asm `fstps  148(%esp)`;
  asm `jmp  .noise3_L5`;
}

bool setupNoiseContext;
NoiseContext nc;

float noise3(vec3f v) {
  if !setupPerm permsetup;
  if (!setupNoiseContext) {
    setupNoiseContext = true;
    auto array = [
      [[1, 0, 0, 0], [1, 1, 0, 0]],
      [[0, 1, 0, 0], [1, 1, 0, 0]],
      [[0, 0, 0, 0], [0, 0, 0, 0]],
      [[0, 1, 0, 0], [0, 1, 1, 0]],
      [[1, 0, 0, 0], [1, 0, 1, 0]],
      [[0, 0, 0, 0], [0, 0, 0, 0]],
      [[0, 0, 1, 0], [1, 0, 1, 0]],
      [[0, 0, 1, 0], [0, 1, 1, 0]]
    ];
    for auto tup1 <- zip(0..-1, array) {
      for auto tup2 <- zip(0..-1, tup1[1]) {
        for auto tup3 <- zip(0..-1, tup2[1]) {
          nc.offsets[tup1[0]][tup2[0]][tup3[0]] = tup3[1];
        }
      }
    }
    nc.perm = (new byte[] 256).ptr;
    nc.mperm = (new byte[] 256).ptr;
    for int i <- 0..256 {
      nc.perm[i] = byte:char:short:perm[i];
      nc.mperm[i] = byte:char:short:mperm[i];
    }
  }
  return noise3_asm(v.x, v.y, v.z, &nc);
}

/*
float noise3_alt(vec3f v) {
  vec3f x 4  vs = void;
  vec3f vsum = void;
  int x 4  gi = void;
  int mask = void;
  vec3f v0 = void;
  if !setupPerm permsetup;
  
  vsum = v + (v.sum / 3.0f);
  // copypasted from fastfloor3f
  xmm[4] = vsum;
  asm `cvttps2dq %xmm4, %xmm5`;
  asm `psrld $31, %xmm4`;
  asm `psubd %xmm4, %xmm5`;
  auto indices = vec3i:xmm[5];
  vs[0] = v - indices      + vec3f(indices.sum / 6.0f);
  xmm[6] = vec4f:vs[0];
  vs[1] = xmm[6] + vec4f(1.0f / 6);
  vs[2] = xmm[6] + vec4f(2.0f / 6);
  vs[3] = xmm[6] + vec4f(-1 + 3.0f / 6);
  xmm[4] = xmm[6].xxy;
  xmm[5] = xmm[6].yzz;
  // this is correct, I worked it out
  // mask = [0b100_110, 0b010_110, 0, 0b010_011, 0b100_101, 0, 0b001_101, 0b001_011][(eval xmm[4] < xmm[5]) & 0b0111];
  auto opp = &offsets[(eval xmm[4] < xmm[5]) & 0b0111];
  alias op = *opp;
  alias offs1 = op[0];
  alias offs2 = op[1];
  vs[1] -= vec3f(offs1);
  vs[2] -= vec3f(offs2);
  auto ii = indices.x, jj = indices.y, kk = indices.z;
  alias i1 = offs1.x, i2 = offs2.x,
        j1 = offs1.y, j2 = offs2.y,
        k1 = offs1.z, k2 = offs2.z;
  {
    auto lperm = perm.ptr;
    auto mperm = mperm.ptr;
    gi[0] = mperm[(lperm[(lperm[(kk   )&0xff]+jj   )&0xff]+ii   )&0xff];
    gi[1] = mperm[(lperm[(lperm[(kk+k1)&0xff]+jj+j1)&0xff]+ii+i1)&0xff];
    gi[2] = mperm[(lperm[(lperm[(kk+k2)&0xff]+jj+j2)&0xff]+ii+i2)&0xff];
    gi[3] = mperm[(lperm[(lperm[(kk+1 )&0xff]+jj+1 )&0xff]+ii+1 )&0xff];
  }
  vec3f current = void;
  vec4f factors = void, res = void;
  auto pair = [1f, -1f, -1f];
  while (int c <- 0..4) {
    auto vscp = &vs[c];
    alias vsc = *vscp;
    current = vsc;
    current *= current;
    factors[c] = 0.6f - current.sum;
    if (factors[c] >= 0) {
      auto id = gi[c];
      res[c] = (vsc[id >> 3] * pair[id&1]) + (vsc[((id >> 2) | (id >> 3)) & 1 + 1] * pair[id&2]);
    } else {
      factors[c] = 0;
      res[c] = 0;
    }
  }
  xmm[4] = factors;
  xmm[4] *= xmm[4];
  xmm[4] *= xmm[4];
  res *= xmm[4];
  return 0.5f + 16.0f*res.sum;
}
*/
