# Correctness Proof of AES GCM SIV

[![Build Status](https://travis-ci.org/GaloisInc/AES-GCM-SIV-proof.svg?branch=master)](https://travis-ci.org/GaloisInc/AES-GCM-SIV-proof)

This repository contains the specification and correctness proof for the reference implementation of AES GCM SIV. Right now it verifies our fork of the code, which has a few verifiability changes (we don't think they change functionality). 

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

Run make in the directory you wish to run the proof for.

## Specification

The specification is in the [cryptol-specs](proof/cryptol-specs/) directory.

## Proof

- [proof.saw](proof/ref-128/proof.saw) the top level proof file that loads the C code and all of the SAW scripts, running the proofs in the process
- [GCM_SIV_C.saw](proof/ref-128/GCM_SIV_C.saw) main proof file with proofs for
  - key expansion
  - AES_128 encryption
  - gfmul_int (multiplication in a galois field)
  - POLYVAL
  - AES_128_CTR (CTR instantiated with the AES_128 function)
  - GCM_SIV_ENC_2_Keys, the top-level theorem of this proof
- [aes_emulation.saw](proof/ref-128/aes_emulation.saw) has definitions for state functions, and proofs of row-shifting and substitute-bytes functions
- [clmul-emulator.saw](proof/ref-128/clmul_emulator.saw) contains proofs for functions `mul` and `vcmul_emulator`.
- [common.saw](proof/ref-128/common.saw) utility functions to make the SAW proofs pretty