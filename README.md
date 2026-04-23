g++ -O3 -std=c++17 -fopenmp <code_filename>.cpp -o <binary_filename> -I/usr/local/include/pbc -L/usr/local/lib -lpbc -lgmp -lcrypto
time ./<binary_filename>