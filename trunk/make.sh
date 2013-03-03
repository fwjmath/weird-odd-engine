g++ -o trn/trn.o -c -O3 trn/trn.c
g++ -O3 -o weirdodd trn/trn.o weirdodd.cpp -lgmp -g -static

