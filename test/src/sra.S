	.section .text.entry
	.globl _start

_start:

	#-------------------------------------------------------------
	# Arithmetic tests
	#-------------------------------------------------------------

test_2: 
	li gp, 2; 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_3: 
	li gp, 3; 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((1) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0xffffffffc0000000) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_4: 
	li gp, 4; 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((7) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0xffffffffff000000) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_5: 
	li gp, 5; 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((14) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0xfffffffffffe0000) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_6: 
	li gp, 6; 
	li x1, ((0xffffffff80000001) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((31) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0xffffffffffffffff) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;

test_7: 
	li gp, 7; 
	li x1, ((0x000000007fffffff) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0x000000007fffffff) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_8: 
	li gp, 8; 
	li x1, ((0x000000007fffffff) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((1) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0x000000003fffffff) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_9: 
	li gp, 9; 
	li x1, ((0x000000007fffffff) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((7) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0x0000000000ffffff) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_10: 
	li gp, 10; 
	li x1, ((0x000000007fffffff) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((14) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0x000000000001ffff) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_11: 
	li gp, 11; 
	li x1, ((0x000000007fffffff) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((31) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0x0000000000000000) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;

test_12: 
	li gp, 12; 
	li x1, ((0xffffffff81818181) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0xffffffff81818181) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_13: 
	li gp, 13; 
	li x1, ((0xffffffff81818181) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((1) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0xffffffffc0c0c0c0) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_14: 
	li gp, 14; 
	li x1, ((0xffffffff81818181) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((7) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0xffffffffff030303) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_15: 
	li gp, 15; 
	li x1, ((0xffffffff81818181) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((14) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0xfffffffffffe0606) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_16: 
	li gp, 16; 
	li x1, ((0xffffffff81818181) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((31) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0xffffffffffffffff) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;

	# Verify that shifts only use bottom six(rv64) or five(rv32) bits

test_17: 
	li gp, 17; 
	li x1, ((0xffffffff81818181) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0xffffffffffffffc0) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0xffffffff81818181) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_18: 
	li gp, 18; 
	li x1, ((0xffffffff81818181) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0xffffffffffffffc1) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0xffffffffc0c0c0c0) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_19: 
	li gp, 19; 
	li x1, ((0xffffffff81818181) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0xffffffffffffffc7) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0xffffffffff030303) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_20: 
	li gp, 20; 
	li x1, ((0xffffffff81818181) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0xffffffffffffffce) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0xfffffffffffe0606) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_21: 
	li gp, 21; 
	li x1, ((0xffffffff81818181) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0xffffffffffffffff) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2;; 
	li x7, ((0xffffffffffffffff) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;

	#-------------------------------------------------------------
	# Source/Destination tests
	#-------------------------------------------------------------

test_22: 
	li gp, 22; 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((7) & ((1 << (32 - 1) << 1) - 1)); 
	sra x1, x1, x2;; 
	li x7, ((0xffffffffff000000) & ((1 << (32 - 1) << 1) - 1)); 
	bne x1, x7, fail;;
test_23: 
	li gp, 23; 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((14) & ((1 << (32 - 1) << 1) - 1)); 
	sra x2, x1, x2;; 
	li x7, ((0xfffffffffffe0000) & ((1 << (32 - 1) << 1) - 1)); 
	bne x2, x7, fail;;
test_24: 
	li gp, 24; 
	li x1, ((7) & ((1 << (32 - 1) << 1) - 1)); 
	sra x1, x1, x1;; 
	li x7, ((0) & ((1 << (32 - 1) << 1) - 1)); 
	bne x1, x7, fail;;

	#-------------------------------------------------------------
	# Bypassing tests
	#-------------------------------------------------------------

test_25: 
	li gp, 25; 
	li x4, 0; 
1: 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((7) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2; 
	addi x6, x14, 0; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0xffffffffff000000) & ((1 << (32 - 1) << 1) - 1)); 
	bne x6, x7, fail;;
test_26: 
	li gp, 26; 
	li x4, 0; 
1: 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((14) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2; 
	nop; 
	addi x6, x14, 0; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0xfffffffffffe0000) & ((1 << (32 - 1) << 1) - 1)); 
	bne x6, x7, fail;;
test_27: 
	li gp, 27; 
	li x4, 0; 
1: 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((31) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2; 
	nop; 
	nop; 
	addi x6, x14, 0; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0xffffffffffffffff) & ((1 << (32 - 1) << 1) - 1)); 
	bne x6, x7, fail;;

test_28: 
	li gp, 28; 
	li x4, 0; 
1: 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((7) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0xffffffffff000000) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_29: 
	li gp, 29; 
	li x4, 0; 
1: 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((14) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	sra x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0xfffffffffffe0000) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_30: 
	li gp, 30; 
	li x4, 0; 
1: 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((31) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	nop; 
	sra x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0xffffffffffffffff) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_31: 
	li gp, 31; 
	li x4, 0; 
1: 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	li x2, ((7) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0xffffffffff000000) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_32: 
	li gp, 32; 
	li x4, 0; 
1: 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	li x2, ((14) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	sra x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0xfffffffffffe0000) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_33: 
	li gp, 33; 
	li x4, 0; 
1: 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	nop; 
	li x2, ((31) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0xffffffffffffffff) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;

test_34: 
	li gp, 34; 
	li x4, 0; 
1: 
	li x2, ((7) & ((1 << (32 - 1) << 1) - 1)); 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0xffffffffff000000) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_35: 
	li gp, 35; 
	li x4, 0; 
1: 
	li x2, ((14) & ((1 << (32 - 1) << 1) - 1)); 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	sra x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0xfffffffffffe0000) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_36: 
	li gp, 36; 
	li x4, 0; 
1: 
	li x2, ((31) & ((1 << (32 - 1) << 1) - 1)); 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	nop; 
	sra x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0xffffffffffffffff) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_37: 
	li gp, 37; 
	li x4, 0; 
1: 
	li x2, ((7) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0xffffffffff000000) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_38: 
	li gp, 38; 
	li x4, 0; 
1: 
	li x2, ((14) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	sra x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0xfffffffffffe0000) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_39: 
	li gp, 39; 
	li x4, 0; 
1: 
	li x2, ((31) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	nop; 
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1)); 
	sra x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0xffffffffffffffff) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;

test_40: 
	li gp, 40; 
	li x1, ((15) & ((1 << (32 - 1) << 1) - 1)); 
	sra x2, x0, x1;; 
	li x7, ((0) & ((1 << (32 - 1) << 1) - 1)); 
	bne x2, x7, fail;;
test_41: 
	li gp, 41; 
	li x1, ((32) & ((1 << (32 - 1) << 1) - 1)); 
	sra x2, x1, x0;; 
	li x7, ((32) & ((1 << (32 - 1) << 1) - 1)); 
	bne x2, x7, fail;;
test_42: 
	li gp, 42; 
	sra x1, x0, x0;; 
	li x7, ((0) & ((1 << (32 - 1) << 1) - 1)); 
	bne x1, x7, fail;;
test_43: 
	li gp, 43; 
	li x1, ((1024) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((2048) & ((1 << (32 - 1) << 1) - 1)); 
	sra x0, x1, x2;; 
	li x7, ((0) & ((1 << (32 - 1) << 1) - 1)); 
	bne x0, x7, fail;;

	
success:
	la x1,  data      ;
	li x31, 0x11111111;
	sw x31, 0(x1)     ;
	j trap		  ;

fail:
	la x1, data       ;	
	li x31, 0xFFFFFFFF;
	sw x31, 0(x1)	  ;

trap:	j trap;

	.section .data.entry
	.global data
data:
	.space 128 * 4
	.space 128 * 4
	.global data_end
data_end:	
	
