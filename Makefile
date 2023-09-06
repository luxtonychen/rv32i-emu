CC            = gcc
RV32_CC       = riscv32-unknown-elf-gcc
C_PATH        = ./src/c
IDRIS_PATH    = ./src/idris
LIB_PATH      = ./lib
TEST_ROOT = ./test
TSET_SRC = ./test/src
TEST_BIN = ./test/bin
TEST_ENV = ./test/env

.PHONY: test clean

all: lib test

lib: lib_mem lib_bits
	cp $(LIB_PATH)/*.so $(IDRIS_PATH)/

lib_mem: $(C_PATH)/lib_mem.c lib_bits
	$(CC) -shared $(LIB_PATH)/lib_bits_vec.so $(C_PATH)/lib_mem.c -o $(LIB_PATH)/lib_mem.so

lib_bits: $(C_PATH)/lib_bits_vec.c
	$(CC) -shared $(C_PATH)/lib_bits_vec.c -o $(LIB_PATH)/lib_bits_vec.so

test:
	cd $(TEST_ROOT) && ./asm2bin.sh && cd ..

clean:
	rm -rf $(LIB_PATH)/*.so
	rm -rf $(IDRIS_PATH)/*.so
	rm -rf $(IDRIS_PATH)/*.bin
	rm -rf $(TEST_BIN)/*.o
	rm -rf $(TEST_BIN)/*.bin	
