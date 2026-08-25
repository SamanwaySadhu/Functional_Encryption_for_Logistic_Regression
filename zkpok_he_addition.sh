#!/usr/bin/env bash

set -euo pipefail

g++ -O3 -std=c++17 -fopenmp zkpok_he_addition.cpp -o zkpok_he_addition -lcrypto -lgmp

DIM="${1:-8}"
./zkpok_he_addition "$DIM"
