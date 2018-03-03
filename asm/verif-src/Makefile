.PHONY: clean

proof_target: \
  GCM_SIV.h GCM_SIV.c main.c \
  polyval_horner.s polyval_htble.s dec_msg_htable_x6.s \
  enc_msg_x4.s enc_msg_x8.s \
  key_expands_and_enc.s
	gcc -no-pie -O3 -maes -mavx -w $^ -o $@

clean:
	rm proof_target


