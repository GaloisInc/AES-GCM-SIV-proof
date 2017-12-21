#include <emmintrin.h>
#include <wmmintrin.h>
#include <tmmintrin.h>

__m128i _s_mm_setr_epi32(int i0, int i1, int i2, int i3);

void _s_mm_storeu_si128(__m128i *p, __m128i a);

__m128i _s_mm_loadu_si128(__m128i const *p);
__m128i _s_mm_clmulepi64_si128(__m128i v1,
                               __m128i v2,
                               const int imm8);


__m128i _s_mm_xor_si128 ( __m128i a, __m128i b);

__m128i _s_mm_slli_si128(__m128i a, int imm);

__m128i _s_mm_srli_si128(__m128i a, int imm);

__m128i _s_mm_shuffle_epi32 (__m128i a, int imm);

