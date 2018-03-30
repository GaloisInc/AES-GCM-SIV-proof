.PHONY: clean

CC=gcc-7
CFLAGS=-Wall -Wextra -no-pie -O2 -maes -mavx -fno-stack-protector

proof_target: \
  GCM_SIV.h GCM_SIV.c main.c \
  polyval_horner.s polyval_htble.s dec_msg_htable_x6.s \
  enc_msg_x4.s enc_msg_x8.s \
  key_expands_and_enc.s
	$(CC) $(CFLAGS) $^ -o $@

clean:
	rm proof_target


