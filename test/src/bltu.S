	.section .text.entry
	.globl _start

_start:
	#-------------------------------------------------------------
	# Branch tests
	#-------------------------------------------------------------

	# Each test checks both forward and backward branches

test_2:
	li gp, 2; 
	li x1, 0x00000000; 
	li x2, 0x00000001; 
	bltu x1, x2, 2f; 
	bne x0, gp, fail; 
1:
	bne x0, gp, 3f; 
2:
	bltu x1, x2, 1b; 
	bne x0, gp, fail; 
3:;
test_3:
	li gp, 3; 
	li x1, 0xfffffffe; 
	li x2, 0xffffffff; 
	bltu x1, x2, 2f; 
	bne x0, gp, fail; 
1:
	bne x0, gp, 3f; 
2:
	bltu x1, x2, 1b; 
	bne x0, gp, fail; 
3:;
test_4:
	li gp, 4; 
	li x1, 0x00000000; 
	li x2, 0xffffffff; 
	bltu x1, x2, 2f; 
	bne x0, gp, fail; 
1:
	bne x0, gp, 3f; 
2:
	bltu x1, x2, 1b; 
	bne x0, gp, fail; 
3:;

test_5:
	li gp, 5; 
	li x1, 0x00000001; 
	li x2, 0x00000000; 
	bltu x1, x2, 1f; 
	bne x0, gp, 2f; 
1:
	bne x0, gp, fail; 
2:
	bltu x1, x2, 1b; 
3:;
test_6:
	li gp, 6; 
	li x1, 0xffffffff; 
	li x2, 0xfffffffe; 
	bltu x1, x2, 1f; 
	bne x0, gp, 2f; 
1:
	bne x0, gp, fail; 
2:
	bltu x1, x2, 1b; 
3:;
test_7:
	li gp, 7; 
	li x1, 0xffffffff; 
	li x2, 0x00000000; 
	bltu x1, x2, 1f; 
	bne x0, gp, 2f; 
1:
	bne x0, gp, fail; 
2:
	bltu x1, x2, 1b; 
3:;
test_8:
	li gp, 8; 
	li x1, 0x80000000; 
	li x2, 0x7fffffff; 
	bltu x1, x2, 1f; 
	bne x0, gp, 2f; 
1:
	bne x0, gp, fail; 
2:
	bltu x1, x2, 1b; 
3:;

	#-------------------------------------------------------------
	# Bypassing tests
	#-------------------------------------------------------------

test_9:
	li gp, 9; 
	li x4, 0; 
1:
	li x1, 0xf0000000; 
	li x2, 0xefffffff; 
	bltu x1, x2, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_10:
	li gp, 10; 
	li x4, 0; 
1:
	li x1, 0xf0000000; 
	li x2, 0xefffffff; 
	nop; 
	bltu x1, x2, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_11:
	li gp, 11; 
	li x4, 0; 
1:
	li x1, 0xf0000000; 
	li x2, 0xefffffff; 
	nop; 
	nop; 
	bltu x1, x2, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_12:
	li gp, 12; 
	li x4, 0; 
1:
	li x1, 0xf0000000; 
	nop; 
	li x2, 0xefffffff; 
	bltu x1, x2, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_13:
	li gp, 13; 
	li x4, 0; 
1:
	li x1, 0xf0000000; 
	nop; 
	li x2, 0xefffffff; 
	nop; 
	bltu x1, x2, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_14:
	li gp, 14; 
	li x4, 0; 
1:
	li x1, 0xf0000000; 
	nop; 
	nop; 
	li x2, 0xefffffff; 
	bltu x1, x2, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;

test_15:
	li gp, 15; 
	li x4, 0; 
1:
	li x1, 0xf0000000; 
	li x2, 0xefffffff; 
	bltu x1, x2, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_16:
	li gp, 16; 
	li x4, 0; 
1:
	li x1, 0xf0000000; 
	li x2, 0xefffffff; 
	nop; 
	bltu x1, x2, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_17:
	li gp, 17; 
	li x4, 0; 
1:
	li x1, 0xf0000000; 
	li x2, 0xefffffff; 
	nop; 
	nop; 
	bltu x1, x2, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_18:
	li gp, 18; 
	li x4, 0; 
1:
	li x1, 0xf0000000; 
	nop; 
	li x2, 0xefffffff; 
	bltu x1, x2, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_19:
	li gp, 19; 
	li x4, 0; 
1:
	li x1, 0xf0000000; 
	nop; 
	li x2, 0xefffffff; 
	nop; 
	bltu x1, x2, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_20:
	li gp, 20; 
	li x4, 0; 
1:
	li x1, 0xf0000000; 
	nop; 
	nop; 
	li x2, 0xefffffff; 
	bltu x1, x2, fail; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;

	#-------------------------------------------------------------
	# Test delay slot instructions not executed nor bypassed
	#-------------------------------------------------------------

test_21:
	li gp, 21; 
	li x1, 1; 
	bltu x0, x1, 1f; 
	addi x1, x1, 1; 
	addi x1, x1, 1; 
	addi x1, x1, 1; 
	addi x1, x1, 1; 
1:
	addi x1, x1, 1; 
	addi x1, x1, 1;; 
	li x7, ((3) & ((1 << (32 - 1) << 1) - 1)); 
	bne x1, x7, fail;

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
	.space 256 * 4
	.global data_end
data_end:	
	
	
