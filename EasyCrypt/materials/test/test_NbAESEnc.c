#include <smmintrin.h>
#include <immintrin.h>
#include <stdalign.h>
#include <stdio.h>

typedef unsigned char byte;

int8_t kb[] = { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 
             0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f };

int8_t nb[] = { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 
             0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x1f };

int8_t pb[] = { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 
             0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x2f };

extern __m128i enc(__m128i k, __m128i n,__m128i p);
extern __m128i dec(__m128i k, __m128i n,__m128i c);

int main() {
    __m128i c, pp, p, k, n;

    k = _mm_loadu_si128((__m128i *) kb);
    n = _mm_loadu_si128((__m128i *) nb);
    p = _mm_loadu_si128((__m128i *) pb);

    c = enc(k,n,p);
    pp = dec(k,n,c);

    __m128i neq = _mm_xor_si128(p,pp);
    if(_mm_test_all_zeros(neq,neq)) {
        printf("Verify output: OK!\n");
    }
    else {
        printf("Verify output: Not OK!\n");
    }

    return 0;
}
