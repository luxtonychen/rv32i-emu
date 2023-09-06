	.section .text.entry
	.globl _start

_start:
	#-------------------------------------------------------------
	# Basic tests
	#-------------------------------------------------------------

test_2: 
	li gp, 2; 
	la x1, tdat; 
	li x2, 0x00000000000000aa; 
	la x15, 7f; 
	sh x2, 0(x1); 
	lh x14, 0(x1); 
	j 8f; 
7: 
	mv x14, x2; 
8:; 
	li x7, ((0x00000000000000aa) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_3: 
	li gp, 3; 
	la x1, tdat; 
	li x2, 0xffffffffffffaa00; 
	la x15, 7f; 
	sh x2, 2(x1); 
	lh x14, 2(x1); 
	j 8f; 
7: 
	mv x14, x2; 
8:; 
	li x7, ((0xffffffffffffaa00) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_4: 
	li gp, 4; 
	la x1, tdat; 
	li x2, 0xffffffffbeef0aa0; 
	la x15, 7f; 
	sh x2, 4(x1); 
	lw x14, 4(x1); 
	j 8f; 
7: 
	mv x14, x2; 
8:; 
	li x7, ((0xffffffffbeef0aa0) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_5: 
	li gp, 5; 
	la x1, tdat; 
	li x2, 0xffffffffffffa00a; 
	la x15, 7f; 
	sh x2, 6(x1); 
	lh x14, 6(x1); 
	j 8f; 
7: 
	mv x14, x2; 
8:; 
	li x7, ((0xffffffffffffa00a) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;

	# Test with negative offset

test_6: 
	li gp, 6; 
	la x1, tdat8; 
	li x2, 0x00000000000000aa; 
	la x15, 7f; 
	sh x2, -6(x1); 
	lh x14, -6(x1); 
	j 8f; 
7: 
	mv x14, x2; 
8:; 
	li x7, ((0x00000000000000aa) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_7: 
	li gp, 7; 
	la x1, tdat8; 
	li x2, 0xffffffffffffaa00; 
	la x15, 7f; 
	sh x2, -4(x1); 
	lh x14, -4(x1); 
	j 8f; 
7: 
	mv x14, x2; 
8:; 
	li x7, ((0xffffffffffffaa00) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_8: 
	li gp, 8; 
	la x1, tdat8; 
	li x2, 0x0000000000000aa0; 
	la x15, 7f; 
	sh x2, -2(x1); 
	lh x14, -2(x1); 
	j 8f; 
7: 
	mv x14, x2; 
8:; 
	li x7, ((0x0000000000000aa0) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_9: 
	li gp, 9; 
	la x1, tdat8; 
	li x2, 0xffffffffffffa00a; 
	la x15, 7f; 
	sh x2, 0(x1); 
	lh x14, 0(x1); 
	j 8f; 
7: 
	mv x14, x2; 
8:; 
	li x7, ((0xffffffffffffa00a) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;

	# Test with a negative base

test_10: 
	li gp, 10; 
	la x1, tdat9; 
	li x2, 0x12345678; 
	addi x4, x1, -32; 
	sh x2, 32(x4); 
	lh x5, 0(x1);; 
	li x7, ((0x5678) & ((1 << (32 - 1) << 1) - 1)); 
	bne x5, x7, fail;







	# Test with unaligned base

test_11: 
	li gp, 11; 
	la x1, tdat9; 
	li x2, 0x00003098; 
	addi x1, x1, -5; 
	sh x2, 7(x1); 
	la x4, tdat10; 
	lh x5, 0(x4);; 
	li x7, ((0x3098) & ((1 << (32 - 1) << 1) - 1)); 
	bne x5, x7, fail;
	# 53 "../rv64ui/sh.S"
	#-------------------------------------------------------------
	# Bypassing tests
	#-------------------------------------------------------------

test_12: 
	li gp, 12; 
	li x4, 0; 
1: 
	li x1, 0xffffffffffffccdd; 
	la x2, tdat; 
	sh x1, 0(x2); 
	lh x14, 0(x2); 
	li x7, 0xffffffffffffccdd; 
	bne x14, x7, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_13: 
	li gp, 13; 
	li x4, 0; 
1: 
	li x1, 0xffffffffffffbccd; 
	la x2, tdat; 
	nop; 
	sh x1, 2(x2); 
	lh x14, 2(x2); 
	li x7, 0xffffffffffffbccd; 
	bne x14, x7, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_14: 
	li gp, 14; 
	li x4, 0; 
1: 
	li x1, 0xffffffffffffbbcc; 
	la x2, tdat; 
	nop; 
	nop; 
	sh x1, 4(x2); 
	lh x14, 4(x2); 
	li x7, 0xffffffffffffbbcc; 
	bne x14, x7, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_15: 
	li gp, 15; 
	li x4, 0; 
1: 
	li x1, 0xffffffffffffabbc; 
	nop; 
	la x2, tdat; 
	sh x1, 6(x2); 
	lh x14, 6(x2); 
	li x7, 0xffffffffffffabbc; 
	bne x14, x7, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_16: 
	li gp, 16; 
	li x4, 0; 
1: 
	li x1, 0xffffffffffffaabb; 
	nop; 
	la x2, tdat; 
	nop; 
	sh x1, 8(x2); 
	lh x14, 8(x2); 
	li x7, 0xffffffffffffaabb; 
	bne x14, x7, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_17: 
	li gp, 17; 
	li x4, 0; 
1: 
	li x1, 0xffffffffffffdaab; 
	nop; 
	nop; 
	la x2, tdat; 
	sh x1, 10(x2); 
	lh x14, 10(x2); 
	li x7, 0xffffffffffffdaab; 
	bne x14, x7, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;

test_18: 
	li gp, 18; 
	li x4, 0; 
1: 
	la x2, tdat; 
	li x1, 0x2233; 
	sh x1, 0(x2); 
	lh x14, 0(x2); 
	li x7, 0x2233; 
	bne x14, x7, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_19: 
	li gp, 19; 
	li x4, 0; 
1: 
	la x2, tdat; 
	li x1, 0x1223; 
	nop; 
	sh x1, 2(x2); 
	lh x14, 2(x2); 
	li x7, 0x1223; 
	bne x14, x7, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_20: 
	li gp, 20; 
	li x4, 0; 
1: 
	la x2, tdat; 
	li x1, 0x1122; 
	nop; 
	nop; 
	sh x1, 4(x2); 
	lh x14, 4(x2); 
	li x7, 0x1122; 
	bne x14, x7, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_21: 
	li gp, 21; 
	li x4, 0; 
1: 
	la x2, tdat; 
	nop; 
	li x1, 0x0112; 
	sh x1, 6(x2); 
	lh x14, 6(x2); 
	li x7, 0x0112; 
	bne x14, x7, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_22: 
	li gp, 22; 
	li x4, 0; 
1: 
	la x2, tdat; 
	nop; 
	li x1, 0x0011; 
	nop; 
	sh x1, 8(x2); 
	lh x14, 8(x2); 
	li x7, 0x0011; 
	bne x14, x7, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_23: 
	li gp, 23; 
	li x4, 0; 
1: 
	la x2, tdat; 
	nop; 
	nop; 
	li x1, 0x3001; 
	sh x1, 10(x2); 
	lh x14, 10(x2); 
	li x7, 0x3001; 
	bne x14, x7, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;

	li a0, 0xbeef
	la a1, tdat
	sh a0, 6(a1)
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
tdat:
tdat1: 
.half 0xbeef
tdat2: 
.half 0xbeef
tdat3: 
.half 0xbeef
tdat4: 
.half 0xbeef
tdat5: 
.half 0xbeef
tdat6: 
.half 0xbeef
tdat7: 
.half 0xbeef
tdat8: 
.half 0xbeef
tdat9: 
.half 0xbeef
tdat10: 
.half 0xbeef

	.align 4;
	.space 128 * 4
	.global data_end
data_end:	
