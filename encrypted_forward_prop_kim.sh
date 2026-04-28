#!/usr/bin/env bash

set -euo pipefail

g++ -O3 -std=c++17 -fopenmp encrypted_forward_prop_kim.cpp -o encrypted_forward_prop_kim -I/usr/local/include/pbc -L/usr/local/lib -lpbc -lgmp -lcrypto

benchmark_log=$(mktemp)
trap 'rm -f "$benchmark_log"' EXIT

for i in $(seq 1 3); do
	echo "======= Run $i ======="
	{ time ./encrypted_forward_prop_kim; } 2>&1 | tee -a "$benchmark_log"
	echo
done

awk '
BEGIN {
	runs = 0
}

match($0, /^KeyGen total: ([0-9.]+) us, average: ([0-9.]+) us$/, m) {
	keygen_total += m[1]
	keygen_avg += m[2]
	runs++
}
match($0, /^Encrypt total: ([0-9.]+) us, average: ([0-9.]+) us$/, m) {
	encrypt_total += m[1]
	encrypt_avg += m[2]
}
match($0, /^Decrypt bilinear parallel loop total: ([0-9.]+) ms, average: ([0-9.]+) ms$/, m) {
	bilinear_total += m[1]
	bilinear_avg += m[2]
}
match($0, /^Decrypt lookup parallel loop total: ([0-9.]+) ms, average: ([0-9.]+) ms$/, m) {
	lookup_total += m[1]
	lookup_avg += m[2]
}
match($0, /^C2 generation parallel loop total: ([0-9.]+) ms, average: ([0-9.]+) ms$/, m) {
	c2_total += m[1]
	c2_avg += m[2]
}
match($0, /^Setup total: ([0-9.]+) ms, average: ([0-9.]+) ms$/, m) {
	setup_total += m[1]
	setup_avg += m[2]
}
match($0, /^LUT build total: ([0-9.]+) ms, average: ([0-9.]+) ms$/, m) {
	lut_total += m[1]
	lut_avg += m[2]
}
match($0, /^Cumulative LUT size: ([0-9.]+) MB$/, m) {
	lut_size += m[1]
}

END {
	if (runs == 0) {
		print "No benchmark rows found to average."
		exit 1
	}

	printf "======= Average Across %d Runs =======\n", runs
	printf "KeyGen total: %.3f us, average: %.3f us\n", keygen_total / runs, keygen_avg / runs
	printf "Encrypt total: %.3f us, average: %.3f us\n", encrypt_total / runs, encrypt_avg / runs
	printf "Decrypt bilinear parallel loop total: %.3f ms, average: %.3f ms\n", bilinear_total / runs, bilinear_avg / runs
	printf "Decrypt lookup parallel loop total: %.3f ms, average: %.3f ms\n", lookup_total / runs, lookup_avg / runs
	printf "C2 generation parallel loop total: %.3f ms, average: %.3f ms\n", c2_total / runs, c2_avg / runs
	printf "Setup total: %.3f ms, average: %.3f ms\n", setup_total / runs, setup_avg / runs
	printf "LUT build total: %.3f ms, average: %.3f ms\n", lut_total / runs, lut_avg / runs
	printf "Cumulative LUT size: %.6f MB\n", lut_size / runs
}
' "$benchmark_log"
