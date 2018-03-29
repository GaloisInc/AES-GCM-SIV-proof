#include "GCM_SIV.h"
/* This is just a wrapper, so that we have all funcionts linked in
   a single executable */

// #define DEBUG

#ifdef DEBUG
#include <stdio.h>
#endif

#ifdef DEBUG
void print_hex(uint8_t* bytes, size_t size){
  for(uint64_t i = 0; i < size; ++i) {
    printf("0x%02x, ", (uint8_t)bytes[i] & (uint8_t)0xff);
    if (i % 16 ==15) printf("\n");
  }
  printf("\n");
}

#endif
int main(int argc, char* argv[]) {
  (void) argc;
  (void) argv;


#ifdef DEBUG
  uint8_t keys[11 * 16] = { 0 };
  uint8_t iv[12] = { 0 } ;
  uint8_t aad[4] = { 0 } ;
  uint8_t msg[24] = { 0 } ;
  uint8_t ct [24] = { 0 } ;
  uint8_t tag [16] = { 0 } ;
  int i = 0;

  AES_GCM_SIV_Encrypt ((AES_GCM_SIV_CONTEXT*) keys, ct, tag, aad, msg, 4, 24, iv, NULL);

  for (i = 0; i < 24; ++i)
    printf ("%x ", ct[i]);
  printf ("\n");
  return 0;

#endif

  AES_GCM_SIV_Encrypt(0,0,0,0,0,0,0,0,0);
  AES_GCM_SIV_Decrypt(0,0,0,0,0,0,0,0,0);
  return 0;
}
