CLANG=clang-3.8
LLVM_LINK=llvm-link-3.8
SAW=../../bin/saw

all: proof

bitcode/%.bc: bitcode/ ../../AES-GCM-SIV/AES_GCM_SIV_128/AES_GCM_SIV_128_Reference_Code/%.c
	$(CLANG) -g -c -emit-llvm -o $@ $^

.PHONY: proof clean run bitcode/

bitcode/:
	mkdir -p bitcode/

proof: bitcode/ref-128.bc
	$(SAW) proof.saw


# We join all bit-code together, as currently we don't support modular reasoning.
bitcode/ref-128.bc: $(addprefix bitcode/, aes_emulation_tables.bc aes_emulation.bc clmul_emulator.bc GCM_SIV_c.bc)
	$(LLVM_LINK) -o $@ $^

run:
	rm -f src/GCM_SIV_GENERAL_V02_BE
	make -C src
	src/GCM_SIV_GENERAL_V02_BE

clean:
	-rm -f *.bc
	-rm -f bitcode/*.bc




