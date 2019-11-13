# CC = gcc-7
CFLAGS = -Wall -Wextra -no-pie -O2 -maes -mavx -fno-stack-protector
SAW = saw
SRCS = $(shell find verif-src -type f \( -name "*.c" -o -name "*.s" \))
HEADERS = $(shell find verif-src -type f -name "*.h")

.PHONY: all prove clean

all: prove

prove: verif-src/proof_target
	stack build saw-script --only-dependencies
	# stack exec proof

verif-src/proof_target: $(SRCS) $(HEADERS)
	gcc-7 $(CFLAGS) $(SRCS) -o $@

clean:
	rm verif-src/proof_target
