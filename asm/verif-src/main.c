#include "GCM_SIV.h"
// #include <stdio.h>
/* This is just a wrapper, so that we have all funcionts linked in
   a single executable */

int main(int argc, char* argv[]) {
  (void) argc;
  (void) argv;
/*
  uint8_t T[16] = { 0 };
  uint8_t H[16] = { 0 };
  uint8_t I[16]  = { 0 };

  I[15] = 128;

  Polyval_Horner(T,H,I,1);

  for(int i = 0; i < 16; ++i)
    printf("%x ", T[i]);
  printf("\n");
  return 0;
*/
  AES_GCM_SIV_Encrypt(0,0,0,0,0,0,0,0,0);
  AES_GCM_SIV_Decrypt(0,0,0,0,0,0,0,0,0);
  return 0;
}
