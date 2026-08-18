#!/usr/bin/env bash

set -euo pipefail

g++ -O3 -std=c++17 -fopenmp encrypted_forward_prop_kim_multiclass.cpp -o encrypted_forward_prop_kim_multiclass -I/usr/local/include/pbc -L/usr/local/lib -lpbc -lgmp -lcrypto

benchmark_log=$(mktemp)
trap 'rm -f "$benchmark_log"' EXIT

for i in $(seq 1 3); do
	echo "======= Run $i ======="
	{ time ./encrypted_forward_prop_kim_multiclass; } 2>&1 | tee -a "$benchmark_log"
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
match($0, /^Truncation lookup parallel loop total: ([0-9.]+) ms, average: ([0-9.]+) ms$/, m) {
	trunc_lookup_total += m[1]
	trunc_lookup_avg += m[2]
}
match($0, /^Softmax lookup parallel loop total: ([0-9.]+) ms, average: ([0-9.]+) ms$/, m) {
	softmax_lookup_total += m[1]
	softmax_lookup_avg += m[2]
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
match($0, /^Truncation LUT build total: ([0-9.]+) ms, average: ([0-9.]+) ms$/, m) {
	trunc_lut_build_total += m[1]
	trunc_lut_build_avg += m[2]
}
match($0, /^Softmax LUT build total: ([0-9.]+) ms, average: ([0-9.]+) ms$/, m) {
	softmax_lut_build_total += m[1]
	softmax_lut_build_avg += m[2]
}
match($0, /^LUT build total: ([0-9.]+) ms, average: ([0-9.]+) ms$/, m) {
	lut_total += m[1]
	lut_avg += m[2]
}
match($0, /^Truncation LUT cumulative size: ([0-9.]+) MB$/, m) {
	trunc_lut_size += m[1]
}
match($0, /^Softmax LUT cumulative size: ([0-9.]+) MB$/, m) {
	softmax_lut_size += m[1]
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
	printf "Truncation lookup parallel loop total: %.3f ms, average: %.3f ms\n", trunc_lookup_total / runs, trunc_lookup_avg / runs
	printf "Softmax lookup parallel loop total: %.3f ms, average: %.3f ms\n", softmax_lookup_total / runs, softmax_lookup_avg / runs
	printf "Decrypt lookup parallel loop total: %.3f ms, average: %.3f ms\n", lookup_total / runs, lookup_avg / runs
	printf "C2 generation parallel loop total: %.3f ms, average: %.3f ms\n", c2_total / runs, c2_avg / runs
	printf "Setup total: %.3f ms, average: %.3f ms\n", setup_total / runs, setup_avg / runs
	printf "Truncation LUT build total: %.3f ms, average: %.3f ms\n", trunc_lut_build_total / runs, trunc_lut_build_avg / runs
	printf "Softmax LUT build total: %.3f ms, average: %.3f ms\n", softmax_lut_build_total / runs, softmax_lut_build_avg / runs
	printf "LUT build total: %.3f ms, average: %.3f ms\n", lut_total / runs, lut_avg / runs
	printf "Truncation LUT cumulative size: %.6f MB\n", trunc_lut_size / runs
	printf "Softmax LUT cumulative size: %.6f MB\n", softmax_lut_size / runs
	printf "Cumulative LUT size: %.6f MB\n", lut_size / runs
}
' "$benchmark_log"
