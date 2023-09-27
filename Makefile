CC            = gcc
C_PATH        = ./src/c
IDRIS_PATH    = ./src/idris
LIB_PATH      = ./lib
TEST_ROOT     = ./test
TEST_STEPS    = 1000

.PHONY: test clean run_tests

all: lib test rv32i run_tests

run_tests: test rv32i
	cd $(TEST_ROOT) && ./run.sh $(TEST_STEPS) && cd ..

rv32i: $(IDRIS_PATH)/RV32I_Lin.idr lib
	cd $(IDRIS_PATH) && idris2 RV32I_Lin.idr -o rv32i && cd ..

lib: lib_mem lib_bits
	cp $(LIB_PATH)/*.so $(IDRIS_PATH)/

lib_mem: $(C_PATH)/lib_mem.c lib_bits
	$(CC) -shared $(LIB_PATH)/lib_bits_vec.so $(C_PATH)/lib_mem.c -o $(LIB_PATH)/lib_mem.so

lib_bits: $(C_PATH)/lib_bits_vec.c
	$(CC) -shared $(C_PATH)/lib_bits_vec.c -o $(LIB_PATH)/lib_bits_vec.so

test: 
	$(MAKE) -C $(TEST_ROOT)

clean:
	rm -rf $(LIB_PATH)/*.so
	rm -rf $(IDRIS_PATH)/*.so
	rm -rf $(IDRIS_PATH)/*.bin
	$(MAKE) -C $(TEST_ROOT) clean	
