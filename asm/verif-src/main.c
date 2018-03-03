#include "GCM_SIV.h"
/* This is just a wrapper, so that we have all funcionts linked in
   a single executable */

int main(int argc, char* argv) {
  AES_GCM_SIV_Encrypt(0,0,0,0,0,0,0,0,0);
  AES_GCM_SIV_Decrypt(0,0,0,0,0,0,0,0,0);
  return 0;
}
