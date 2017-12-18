#include <emmintrin.h>
#include <wmmintrin.h>
#include <tmmintrin.h>
#include <stdint.h>
#include <stdio.h>

__uint128_t _s_mm_setr_epi32(int i0, int i1, int i2, int i3)
{
  printf("setr");
  //return _mm_setr_epi32(i0, i1, i2, i3);
  //return (__m128i)0;
}

void _s_mm_storeu_si128(__m128i *p, __uint128_t a)
{
  _mm_storeu_si128(p, (__m128i) a);
}

__uint128_t _s_mm_loadu_si128(__m128i const *p)
{
  return (__uint128_t) _mm_loadu_si128(p);
}

__uint128_t _s_mm_clmulepi64_si128(__m128i v1,
                               __m128i v2,
                               const int imm8)
{
  //switch statement so we can have compile time constants for each call
  switch (imm8)
  {
  case 0x00:
    return (__uint128_t) _mm_clmulepi64_si128(v1, v2, 0x00);
    break;

  case 0x11:
    return (__uint128_t) _mm_clmulepi64_si128(v1, v2, 0x11);
    break;

  case 0x10:
    return (__uint128_t) _mm_clmulepi64_si128(v1, v2, 0x10);
    break;

  case 0x01:
    return (__uint128_t) _mm_clmulepi64_si128(v1, v2, 0x01);
    break;
  }
}

__uint128_t _s_mm_xor_si128(__m128i a, __m128i b)
{
  return (__uint128_t) _mm_xor_si128(a, b);
}

__uint128_t _s_mm_slli_si128_8(__m128i a)
{
  return (__uint128_t) _mm_slli_si128(a, 8);
}

__uint128_t _s_mm_srli_si128_8(__m128i a)
{
  return (__uint128_t) _mm_srli_si128(a, 8);
}

__uint128_t _s_mm_shuffle_epi32_78(__m128i a)
{
  return (__uint128_t) _mm_shuffle_epi32(a, 78);
}
