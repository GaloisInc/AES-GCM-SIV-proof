CLANG=clang-4.0
LLVM_LINK=llvm-link-4.0
SAW=saw

%.bc: src/%.c
	$(CLANG) -g -c -emit-llvm -o $@ $^

.PHONY: proof clean

proof: clmul_emulator.bc aes.bc
	# $(SAW) clmul_emulator.saw
	$(SAW) aes.saw

# We join the bit-code files for these modules, so that the symbolic simulator
# can see how the tables are initialized
aes.bc: aes_emulation_tables.bc aes_emulation.bc
	$(LLVM_LINK) -o $@ $^

clean:
	-rm *.bc




