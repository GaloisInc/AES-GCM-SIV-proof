#include "GCM_SIV.h"
/* This is just a wrapper, so that we have all funcionts linked in
   a single executable */

// #define DEBUG

#ifdef DEBUG
#include <stdio.h>
#endif

int main(int argc, char* argv[]) {
  (void) argc;
  (void) argv;

#ifdef DEBUG
  uint64_t aad_len = 18;
  uint64_t pt_len  = 24;
  uint8_t T[16];
  uint8_t H[16];
  uint8_t AAD[aad_len];
  uint8_t PT[pt_len];
  uint64_t LENBLK[2];

  for (int i = 0; i < 16; ++i) T[i] = 0xFF;
  for (int i = 0; i < 16; ++i) H[i] = 0xFF;
  for (uint64_t i = 0; i < aad_len; ++i) AAD[i] = 0xFF;
  for (uint64_t i = 0; i < pt_len ; ++i) PT[i] = 0xFF;
  for (int i = 0; i < 2; ++i) LENBLK[i] = 0xFFFFFFFFFFFFFFFF;

  Polyval_Horner_AAD_MSG_LENBLK(T,H,AAD,aad_len,PT,pt_len,LENBLK);

  for(int i = 0; i < 16; ++i) {
    printf("%x ", T[i]);
  }
  printf("\n");
  return 0;
#endif

  AES_GCM_SIV_Encrypt(0,0,0,0,0,0,0,0,0);
  AES_GCM_SIV_Decrypt(0,0,0,0,0,0,0,0,0);
  return 0;
}
