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
  uint8_t table[8 * 16] = { 0 };
  uint8_t msg[4] = { 0 } ;
  uint8_t T[16] = { 0 };
  int i;

  table[0] = 1;
  table[1] = 1;

  msg[3] = 1;

  Polyval_Htable(table,msg,4,T);

  for (i = 0; i < 16; ++i)
    printf ("%x ", T[i]);
  printf ("\n");
  return 0;

#endif

  AES_GCM_SIV_Encrypt(0,0,0,0,0,0,0,0,0);
  AES_GCM_SIV_Decrypt(0,0,0,0,0,0,0,0,0);
  return 0;
}
