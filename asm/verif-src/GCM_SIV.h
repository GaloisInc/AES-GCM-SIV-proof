/*
###############################################################################
# AES-GCM-SIV developers and authors:                                         #
#                                                                             #
# Shay Gueron,    University of Haifa, Israel and                             #
#                 Intel Corporation, Israel Development Center, Haifa, Israel #
# Adam Langley,   Google                                                      #
# Yehuda Lindell, Bar Ilan University                                         #
###############################################################################
#                                                                             #
# References:                                                                 #
#                                                                             #
# [1] S. Gueron, Y. Lindell, GCM-SIV: Full Nonce Misuse-Resistant             #
# Authenticated Encryption at Under One Cycle per Byte,                       #
# 22nd ACM Conference on Computer and Communications Security,                #
# 22nd ACM CCS: pages 109-119, 2015.                                          #
# [2] S. Gueron, A. Langley, Y. Lindell, AES-GCM-SIV: Nonce Misuse-Resistant  #
# Authenticated Encryption.                                                   #
# https://tools.ietf.org/html/draft-gueron-gcmsiv-02#                         #
###############################################################################
#                                                                             #
###############################################################################
#                                                                             #
# Copyright (c) 2016, Shay Gueron                                             #
#                                                                             #
#                                                                             #
# Permission to use this code for AES-GCM-SIV is granted.                     #
#                                                                             #
# Redistribution and use in source and binary forms, with or without          #
# modification, are permitted provided that the following conditions are      #
# met:                                                                        #
#                                                                             #
# * Redistributions of source code must retain the above copyright notice,    #
#   this list of conditions and the following disclaimer.                     #
#                                                                             #
# * Redistributions in binary form must reproduce the above copyright         #
#   notice, this list of conditions and the following disclaimer in the       #
#   documentation and/or other materials provided with the distribution.      #
#                                                                             #
# * The names of the contributors may not be used to endorse or promote       #
# products derived from this software without specific prior written          #
# permission.                                                                 #
#                                                                             #
###############################################################################
#                                                                             #
###############################################################################
# THIS SOFTWARE IS PROVIDED BY THE AUTHORS ""AS IS"" AND ANY                  #
# EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE           #
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR          #
# PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL INTEL CORPORATION OR              #
# CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,       #
# EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,         #
# PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR          #
# PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF      #
# LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING        #
# NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS          #
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                #
###############################################################################
*/
#ifndef GCM_SIV_H
#define GCM_SIV_H

#include <stdint.h>
#include <stdlib.h>


#if !defined (ALIGN64)
#if defined (__GNUC__)
#  define ALIGN64  __attribute__  ( (aligned (64)))
# else
#  define ALIGN64 __declspec (align (64))
# endif
#endif


typedef struct KEY_SCHEDULE
  {
    ALIGN64 unsigned char KEY[16*15];
    unsigned int nr;
  } ROUND_KEYS;

typedef struct GCM_SIV_CONTEXT
{
  ROUND_KEYS KS;
  uint8_t Htbl[16*8];
  ALIGN64 uint8_t secureBuffer[16*16];
  #ifdef DETAILS
  uint8_t details_info[16*56]; // first 20*16 for enc , last 20*16 for dec
  #endif
}AES_GCM_SIV_CONTEXT;


void AES_GCM_SIV_Encrypt
  ( AES_GCM_SIV_CONTEXT* ctx
  , uint8_t* CT
  , uint8_t* TAG
  , const uint8_t* AAD
  , const uint8_t* PT
  , size_t L1
  , size_t L2
  , const uint8_t* IV
  , const uint8_t* KEY
  );

int AES_GCM_SIV_Decrypt
  ( AES_GCM_SIV_CONTEXT* ctx
  , uint8_t* DT
  , uint8_t* TAG
  , const uint8_t* AAD
  , const uint8_t* CT
  , size_t L1
  , size_t L2
  , const uint8_t* IV
  , const uint8_t* KEY
  );

void Polyval_Horner
  ( unsigned char T[16]       // input/output
  , const unsigned char* H    // H
  , const unsigned char* BUF  // Buffer
  , unsigned int blocks       // Len2
  );


void Polyval_Horner_AAD_MSG_LENBLK
  ( uint8_t T[16]
  , const uint8_t Record_Hash_Key[16]
  , const uint8_t *AAD
  , uint64_t L1
  , const uint8_t* PT
  , uint64_t L2
  , const uint64_t len_blk[2]
  );

void ENC_MSG_x4
  ( const unsigned char* PT
  , unsigned char* CT     //Output
  , unsigned char* TAG
  , unsigned char* KS
  , int byte_len
  );

void ENC_MSG_x8
  ( const unsigned char* PT
  , unsigned char* CT         //Output
  , const unsigned char* TAG
  , const unsigned char* KS
  , int byte_len
  );

void INIT_Htable(uint8_t Htbl[16*8], uint8_t *H);

void Polyval_Htable
  ( uint8_t Htbl[16*8]
  , const uint8_t *MSG
  , uint64_t LEN
  , uint8_t T[16]
  );

void Decrypt_Htable
  ( const unsigned char* CT         //input
  , unsigned char* PT               //output
  , unsigned char POLYVAL_dec[16]   //input/output
  , unsigned char TAG[16]
  , unsigned char Htable[16*8]
  , unsigned char* KS               //Key Schedule for decryption
  , int byte_len
  , unsigned char secureBuffer[16*8]
  );

/*
  This function key expansion (128bit) first key - and encrypt 4 blocks in the following way:
  CT[0] = AES_128(first_key, NONCE[95:0] || 0)
  CT[1] = AES_128(first_key, NONCE[95:0] || 1)
  CT[2] = AES_128(first_key, NONCE[95:0] || 2)
  CT[3] = AES_128(first_key, NONCE[95:0] || 3)
*/
void AES128_KS_ENC_x1_INIT_x4
  ( const unsigned char* NONCE
  , unsigned char* CT
  , unsigned char* KS
  , const unsigned char* first_key
  );


void AES_KS(const unsigned char* key, unsigned char* KS);

void AES_KS_ENC_x1
  ( unsigned char* PT
  , unsigned char* CT
  , int len
  , unsigned char *KS
  , unsigned char* key
  );

void AES_128_ENC_x4
  ( uint8_t *IV
  , unsigned char* PT
  , unsigned char* key
  );



void INIT_Htable_6 (unsigned char* Htbl , unsigned char* H);

int Finalize_Tag
  ( unsigned char* PT
  , unsigned char* CT
  , unsigned char* KS
  , uint8_t* orig_tag
  );

void Clear_SIV_CTX(AES_GCM_SIV_CONTEXT* ctx);
#endif
