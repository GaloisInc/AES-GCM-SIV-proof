CLANG=clang-4.0
SAW=saw

FILES=main.c GCM_SIV_c.c clmul_emulator.c aes_emulation.c aes_emulation_tables.c

%.bc: src/%.c
	$(CLANG) -c -emit-llvm -o $@ $^

.PHONY: proof clean

proof: clmul_emulator.bc
	$(SAW) proof.saw

clean:
	-rm *.bc




