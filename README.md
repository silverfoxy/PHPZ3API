# Compile as shared libary
gcc -I /z3-4.8.6-x64-ubuntu-16.04/include -shared -o test_capi.so -fPIC test_capi.c