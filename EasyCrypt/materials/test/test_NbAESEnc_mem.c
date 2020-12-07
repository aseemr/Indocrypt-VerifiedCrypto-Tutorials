#include <stdio.h>

typedef unsigned char byte;

byte k[] = { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 
             0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f };

byte n[] = { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 
             0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x1f };

byte p[] = { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 
             0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x2f };

extern void enc(byte *cp, byte *kp, byte *np, byte *pp);
extern void dec(byte *pp, byte *kp, byte *np, byte *cp);

int crypto_verify(const byte *x,const byte *y)
{
  unsigned int differentbits = 0;
#define F(i) differentbits |= x[i] ^ y[i];
  F(0)
  F(1)
  F(2)
  F(3)
  F(4)
  F(5)
  F(6)
  F(7)
  F(8)
  F(9)
  F(10)
  F(11)
  F(12)
  F(13)
  F(14)
  F(15)
  return (1 & ((differentbits - 1) >> 8)) - 1;
}

int main() {
    byte c[16], pp[16];

    enc(c,k,n,p);
    dec(pp,k,n,c);

    if (crypto_verify(p,pp) == 0) {
        printf("Verify output: OK!\n");
    }
    else {
        printf("Verify output: Not OK!\n");
    }

    return 0;
}
