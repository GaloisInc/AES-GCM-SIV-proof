CLANG=clang-4.0
LLVM_LINK=llvm-link-4.0
SAW=saw

%.bc: src/%.c
	$(CLANG) -g -c -emit-llvm -o $@ $^

.PHONY: proof clean run

proof: ref-128.bc
	$(SAW) proof.saw

# We join all bit-code together, as currently we don't support modular reasoning.
ref-128.bc: aes_emulation_tables.bc aes_emulation.bc clmul_emulator.bc GCM_SIV_c.bc
	$(LLVM_LINK) -o $@ $^

run:
	rm -f src/GCM_SIV_GENERAL_V02_BE
	make -C src
	src/GCM_SIV_GENERAL_V02_BE

clean:
	-rm *.bc




