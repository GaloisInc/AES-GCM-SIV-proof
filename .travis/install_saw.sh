#!/bin/bash
# This script is provided as-is

set -xe

mkdir -p deps/saw
cd deps/saw

curl https://s3-us-west-2.amazonaws.com/s2n-public-test-dependencies/saw-0.2-2018-01-21-Ubuntu14.04-64.tar.gz > saw.tar.gz;

tar -xzf saw.tar.gz --strip-components=1

bin/saw --version

cd ..

mkdir -p z3/bin
mkdir -p yices/bin
curl --retry 3 https://s3-us-west-2.amazonaws.com/s2n-public-test-dependencies/z3-2017-04-04-Ubuntu14.04-64 --output z3/bin/z3
curl --retry 3 https://s3-us-west-2.amazonaws.com/s2n-public-test-dependencies/yices_smt2-linux-static-2017-06-21 --output yices/bin/yices-smt2
sudo chmod +x z3/bin/z3
sudo chmod +x yices/bin/yices-smt2

z3/bin/z3 --version
yices/bin/yices-smt2 --version

SAW_BIN=$(pwd)/saw/bin
Z3_BIN=$(pwd)/z3/bin
YICES_BIN=$(pwd)/yices/bin

export PATH=$SAW_BIN:$Z3_BIN:$YICES_BIN:$PATH