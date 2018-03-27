#include "GCM_SIV.h"
/* This is just a wrapper, so that we have all funcionts linked in
   a single executable */

//#define DEBUG

#ifdef DEBUG
#include <stdio.h>
#endif

#ifdef DEBUG
void print_hex(uint8_t* bytes, size_t size){
  for(uint64_t i = 0; i < size; ++i) {
    printf("%02x", (uint8_t)bytes[size-i-1] & (uint8_t)0xff);
    if (i % 16 ==15) printf("\n");
  }
  printf("\n");
}

#endif
int main(int argc, char* argv[]) {
  (void) argc;
  (void) argv;


#ifdef DEBUG
  uint8_t htbl[16*8] = {0};
  uint8_t aad[16] = {0};
  size_t L = 16;
  uint8_t result[16] = {0};
  uint8_t Record_Hash_Key[16] = {0};

  for(int i=0; i< 16; i++) Record_Hash_Key[i]=126;
  //for(int i=0; i< 16; i++) result[i]=126;
  //INIT_Htable(htbl, Record_Hash_Key);



    aad[0] = 253;
    aad[1] = 68;
    aad[2] = 33;
    aad[3] = 3;
    aad[4] = 34;
    aad[5] = 164;
    aad[6] = 128;
    aad[7] = 10;
    aad[8] = 129;
    aad[9] = 210;
    aad[10] = 0;
    aad[11] = 88;
    aad[12] = 35;
    aad[13] = 8;
    aad[14] = 147;
    aad[15] = 24;




    result[15] = 56;
    result[14] = 2;
    result[13] = 10;
    result[12] = 160;
    result[11] = 136;
    result[10] = 0;
    result[9]= 210;
    result[8]= 139;
    result[7]= 242;
    result[6]= 251;
    result[5]= 55;
    result[4]= 212;
    result[3]= 71;
    result[2]= 225;
    result[1]= 196;
    result[0]= 121;

    htbl[7] = 89;
    htbl[6] = 100;
    htbl[5] = 251;
    htbl[4] = 189;
    htbl[3] = 29;
    htbl[2] = 172;
    htbl[1] = 137;
    htbl[0] = 219;
    htbl[15]  = 85;
    htbl[14]  = 29;
    htbl[13]  = 82;
    htbl[12]  = 2;
    htbl[11]  = 229;
    htbl[10]  = 190;
    htbl[9] = 119;
    htbl[8] = 29;


  printf ("polyval result: \n");
  printf ("--------------------\n");
  printf ("tbl:\n");
  print_hex(htbl, 16*8);
  printf ("input data:");
  print_hex(aad, L);
  printf ("result before:");
  print_hex(result,16);

  Polyval_Htable(htbl, aad, L, result);

  printf ("result:");
  print_hex(result, 16);

  return 0;

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
