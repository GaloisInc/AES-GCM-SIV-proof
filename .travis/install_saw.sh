#!/bin/bash

# -x prints commands as they run -e causes any error to terminate the script with an error code
set -xe

mkdir -p deps/saw
cd deps/
#Check if the proof tool is already there, in case it was cached
if [ ! -f bin/Proof ]; then
    #Download the proof
    curl https://saw.galois.com/builds/gcm_siv/Proof > bin/Proof;
fi



if [ ! -f z3/bin/z3 ] || [ ! -f yices/bin/yices-smt2 ]; then
    mkdir -p z3/bin
    mkdir -p yices/bin
    curl --retry 3 https://s3-us-west-2.amazonaws.com/s2n-public-test-dependencies/z3-2017-04-04-Ubuntu14.04-64 --output z3/bin/z3
    curl --retry 3 https://s3-us-west-2.amazonaws.com/s2n-public-test-dependencies/yices_smt2-linux-static-2017-06-21 --output yices/bin/yices-smt2
    sudo chmod +x z3/bin/z3
    sudo chmod +x yices/bin/yices-smt2

    z3/bin/z3 --version
    yices/bin/yices-smt2 --version
fi
    PROOF_BIN=$(pwd)/bin
    Z3_BIN=$(pwd)/z3/bin
    YICES_BIN=$(pwd)/yices/bin

    export PATH=$SAW_BIN:$Z3_BIN:$YICES_BIN:$PATH


cd ..

#Turn those back off, so they don't affect our Travis script
set +ex