#!/usr/bin/env bash

set -euo pipefail

# NOTE: at the file's default dimensions (784 -> 196 -> 16, QUANTIZATION_BITS=6),
# Layer 1 alone builds 196 LUTs of ~2017 rows x 784x2 G1 elements each -- expect
# tens of GB of LUT memory/scratch and a multi-hour run (see the LUT sizing
# memo for this architecture). Shrink INPUT_DIM/HIDDEN1_DIM/HIDDEN2_DIM at the
# top of encrypted_finetune_forward_kim.cpp for a fast local smoke test.

g++ -O3 -std=c++17 -fopenmp encrypted_finetune_forward_kim.cpp -o encrypted_finetune_forward_kim -I/usr/local/include/pbc -L/usr/local/lib -lpbc -lgmp -lcrypto

time ./encrypted_finetune_forward_kim
