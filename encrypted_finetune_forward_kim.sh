#!/usr/bin/env bash

set -euo pipefail

# NOTE: at the file's default dimensions (FEATURE_SIZE=5, HIDDEN_SIZE=3,
# OUTPUT_SIZE=3, QUANTIZATION_BITS=6), this builds one LUT per hidden unit
# (BATCH_SIZE = HIDDEN_SIZE of them) of ~2017 rows x OUTPUT_SIZE*HIDDEN_SIZE
# G1 elements each -- well under 1 MB per LUT. Adjust FEATURE_SIZE/
# HIDDEN_SIZE/OUTPUT_SIZE at the top of encrypted_finetune_forward_kim.cpp
# to change problem size; BATCH_SIZE tracks HIDDEN_SIZE automatically and
# should not be edited independently.

g++ -O3 -std=c++17 -fopenmp encrypted_finetune_forward_kim.cpp -o encrypted_finetune_forward_kim -I/usr/local/include/pbc -L/usr/local/lib -lpbc -lgmp -lcrypto

time ./encrypted_finetune_forward_kim
