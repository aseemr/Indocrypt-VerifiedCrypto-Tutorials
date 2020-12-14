#include <smmintrin.h>
#include <immintrin.h>
#include <sys/types.h>
#include <stdalign.h>
#include <stdio.h>
#include <stdint.h>

extern __m128i aes(__m128i k, __m128i n);
extern __m128i invaes(__m128i k, __m128i c);

static inline void native_cpuid(uint32_t *eax, uint32_t *ebx, uint32_t *ecx, uint32_t *edx) {
    asm volatile("cpuid"
                 : "=a" (*eax),
                   "=b" (*ebx),
                   "=c" (*ecx),
                   "=d" (*edx)
                 : "0" (*eax), "2" (*ecx));
}

static void check_cpuflags(void) {
    uint32_t eax = 1, ebx, ecx, edx;
    int arggl = 0;

    native_cpuid(&eax, &ebx, &ecx, &edx);

    if (!(ecx & (1 << 25))) {
      (void) fprintf(stderr,
        "Your CPU does not seem the have the AES instruction set\n");
      arggl += 1;
    }

    if (!(ecx & (1 << 28))) {
      (void) fprintf(stderr,
         "Your CPU does not seem the have the AVX instruction set\n");
      arggl += 1;
    }

    if (arggl) {
      (void) fprintf(stderr,
            "There is a high probability that the program triggers "
            "an \"Illegal instruction\" exception\n");
    }
}

void print_u128(__m128i in) {
    alignas(16) uint16_t v[8];
    _mm_store_si128((__m128i*)v, in);
    printf("v8_u16: %x %x %x %x,  %x %x %x %x\n", v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7]);
}

int main() {
    int8_t enc_key[]    = {0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c};
    int8_t plain[]      = {0x32, 0x43, 0xf6, 0xa8, 0x88, 0x5a, 0x30, 0x8d, 0x31, 0x31, 0x98, 0xa2, 0xe0, 0x37, 0x07, 0x34};
    int8_t cipher[]     = {0x39, 0x25, 0x84, 0x1d, 0x02, 0xdc, 0x09, 0xfb, 0xdc, 0x11, 0x85, 0x97, 0x19, 0x6a, 0x0b, 0x32};

    check_cpuflags();

    printf("Test vector\n");
    __m128i k  = _mm_loadu_si128((__m128i *) enc_key);
    __m128i n  = _mm_loadu_si128((__m128i *) plain);
    __m128i c = _mm_loadu_si128((__m128i *) cipher);
    printf("key "); print_u128(k);
    printf("msg "); print_u128(n);
    printf("cph "); print_u128(c);    

    printf("Jasmin-generated encryption\n");
    __m128i cp = aes(k,n);
    printf("cph "); print_u128(cp);    

    printf("Jasmin-generated decryption\n");
    __m128i mp = invaes(k,c);
    printf("msg "); print_u128(mp);    


    return 0;
}
