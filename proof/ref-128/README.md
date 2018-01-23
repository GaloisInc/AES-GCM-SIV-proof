# Correctness Proof of AES_GCM_SIV_128

This directory contains the specification and correctness proof for AES_GCM_SIV_128.

## Dependencies

Building the proofs requires:
- [clang 4.0](http://releases.llvm.org/4.0.0/tools/clang/docs/ReleaseNotes.html) (others might work, but we've tested it with this one) to build bitcode for our tools to consume
- [llvm4.0](https://releases.llvm.org/4.0.1/docs/ReleaseNotes.html) to link the built bitcode
- [SAW](http://saw.galois.com) commit `48e71b4` obtained from github or nightlies, in order to run the proofs
  - [ubunutu](https://saw.galois.com/builds/nightly/saw-0.2-2017-11-30-Ubuntu14.04-64.tar.gz)
  - [osx](https://saw.galois.com/builds/nightly/saw-0.2-2017-11-30-MacOSX-64.tar.gz)
  - [windows](https://saw.galois.com/builds/nightly/saw-0.2-2017-11-30-Windows10-Pro.zip)
- [Z3](https://github.com/Z3Prover/z3), a dependency of SAW

## Building and running
With the module checked out, first [run the patch](../patch-submodule.sh) in order to apply our recommended changes to the codebase (commands are from this directory)

```bash
../patch_submodule.sh
```
Next run `make` in this directory.

## Specification
The specification is in the [cryptol-specs](../cryptol-specs/) directory, its [README](../cryptol-specs/README.md) describes the spec.

## Proof

- [proof.saw](proof.saw) the top level proof file that loads the C code and all of the SAW scripts, running the proofs in the process
- [GCM_SIV_C.saw](GCM_SIV_C.saw) main proof file with proofs for
  - key expansion
  - AES_128 encryption
  - gfmul_int (multiplication in a galois field)
  - POLYVAL
  - AES_128_CTR (CTR instantiated with the AES_128 function)
  - GCM_SIV_ENC_2_Keys, the top-level theorem of this proof
- [aes_emulation.saw](aes_emulation.saw) has definitions for state functions, and proofs of row-shifting and substitute-bytes functions
- [clmul-emulator.saw](clmul_emulator.saw) contains proofs for functions `mul` and `vcmul_emulator`.
- [common.saw](common.saw) utility functions to make the SAW proofs pretty

