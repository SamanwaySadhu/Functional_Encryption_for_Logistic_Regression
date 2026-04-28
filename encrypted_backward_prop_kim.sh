#!/usr/bin/env bash

set -euo pipefail

g++ -O3 -std=c++17 -fopenmp encrypted_backward_prop_kim.cpp -o encrypted_backward_prop_kim -I/usr/local/include/pbc -L/usr/local/lib -lpbc -lgmp -lcrypto

run_log="$(mktemp)"
trap 'rm -f "$run_log"' EXIT

for i in $(seq 1 5); do
	echo "======= Run $i ======="
	time ./encrypted_backward_prop_kim 2>&1 | tee -a "$run_log"
	echo
done

awk '
BEGIN {
	keygen_total = 0;
	keygen_avg = 0;
	encrypt_total = 0;
	encrypt_avg = 0;
	setup_total = 0;
	lut_total = 0;
	bilinear_total = 0;
	lookup_total = 0;
	ctgen_total = 0;
	lutsize_total = 0;
	n = 0;
}

/^KeyGen total:/ {
	keygen_total += $3;
	keygen_avg += $6;
	n++;
}

/^Encrypt total:/ {
	encrypt_total += $3;
	encrypt_avg += $6;
}

/^Setup total:/ { setup_total += $3; }
/^LUT build total:/ { lut_total += $4; }
/^Total bilinear operations time \(phase 2 \+ phase 6\):/ { bilinear_total += $10; }
/^Total lookup time \(phase 4 \+ phase 7\):/ { lookup_total += $9; }
/^Ciphertext generation time \(phase 9\):/ { ctgen_total += $6; }
/^Cumulative LUT size:/ { lutsize_total += $4; }

END {
	if (n == 0) {
		print "No benchmark summaries found.";
		exit 1;
	}

	printf "=== Average Benchmark Summary (%d runs) ===\n", n;
	printf "KeyGen total: %.3f us, average: %.3f us\n", keygen_total / n, keygen_avg / n;
	printf "Encrypt total: %.3f us, average: %.3f us\n", encrypt_total / n, encrypt_avg / n;
	printf "Setup total: %.3f ms\n", setup_total / n;
	printf "LUT build total: %.3f ms\n", lut_total / n;
	printf "Total bilinear operations time (phase 2 + phase 6): %.3f ms\n", bilinear_total / n;
	printf "Total lookup time (phase 4 + phase 7): %.3f ms\n", lookup_total / n;
	printf "Ciphertext generation time (phase 9): %.3f ms\n", ctgen_total / n;
	printf "Cumulative LUT size: %.6f MB\n", lutsize_total / n;
}
' "$run_log"
