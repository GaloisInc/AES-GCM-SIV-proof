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
  uint64_t pt_len = 24;
  uint8_t PT[pt_len];
  uint8_t CT[pt_len];
  uint8_t TAG[16];
  uint8_t KS[11 * 16];

  for (uint64_t i = 0; i < pt_len; ++i) PT[i] = 0;
  for (uint64_t i = 0; i < pt_len; ++i) CT[i] = 0;
  for (int i = 0; i < 16; ++i) TAG[i] = 0;
  for (int i = 0; i < 11 * 16; ++i) KS[i] = 0;

  ENC_MSG_x4(PT,CT,TAG,KS,pt_len);

  for(uint64_t i = 0; i < pt_len; ++i) {
    printf("%x ", CT[i]);
  }
  printf("\n");
  return 0;
#endif

  AES_GCM_SIV_Encrypt(0,0,0,0,0,0,0,0,0);
  AES_GCM_SIV_Decrypt(0,0,0,0,0,0,0,0,0);
  return 0;
}
