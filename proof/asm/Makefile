CC = gcc-7
CFLAGS = -Wall -Wextra -no-pie -O2 -maes -mavx -fno-stack-protector
SAW = saw
SRCS = $(shell find verif-src -type f \( -name "*.c" -o -name "*.s" \))
HEADERS = $(shell find verif-src -type f -name "*.h")

.PHONY: all prove clean

all: prove

prove: proof_target
	stack exec Proof

proof_target: $(SRCS) $(HEADERS)
	$(CC) $(CFLAGS) $(SRCS) -o $@

clean:
	rm proof_target
