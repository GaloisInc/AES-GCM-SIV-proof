CLANG=clang-4.0
FLAGS= -mpclmul -maes  -mavx -w -DRDTSC -Wa,-q
DEF= -DDETAILS -DADD_INFO
LLVM_LINK=llvm-link-4.0
SAW=saw

%.bc: src/%.c
	$(CLANG) $(FLAGS) $(DEF) -g -c -emit-llvm -o $@ $^

.PHONY: proof clean run

proof: int-128.bc
	$(SAW) proof.saw

# We join all bit-code together, as currently we don't support modular reasoning.
#int-128.bc: GCM_SIV.bc general_functions.bc main.bc polyval.bc enc_msg_x4.bc enc_msg_x8.bc dec_msg_htable_x6.bc key_expands_and_enc.bc
int-128.bc:  saw_intrinsics.bc
	$(LLVM_LINK) -o $@ $^

clean:
	-rm *.bc