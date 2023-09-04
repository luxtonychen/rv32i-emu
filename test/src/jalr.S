	.section .text.entry
	.globl _start

_start:
	#-------------------------------------------------------------
	# Test 2:	Basic test
	#-------------------------------------------------------------

test_2:
	li gp, 2
	li t0, 0
	la t1, target_2

	jalr t0, t1, 0
linkaddr_2:
	j fail

target_2:
	la t1, linkaddr_2
	bne t0, t1, fail

	#-------------------------------------------------------------
	# Test 3:Basic test2, rs = rd
	#-------------------------------------------------------------

test_3:
	li gp, 3
	la t0, target_3

	jalr t0, t0, 0
linkaddr_3:
	j fail

target_3:
	la t1, linkaddr_3
	bne t0, t1, fail

	#-------------------------------------------------------------
	# Bypassing tests
	#-------------------------------------------------------------

test_4:
	li gp, 4; 
	li x4, 0; 
1:
	la x6, 2f; 
	jalr x13, x6, 0; 
	bne x0, gp, fail; 
2:
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_5:
	li gp, 5; 
	li x4, 0; 
1:
	la x6, 2f; 
	nop; 
	jalr x13, x6, 0; 
	bne x0, gp, fail; 
2:
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;
test_6:
	li gp, 6; 
	li x4, 0; 
1:
	la x6, 2f; 
	nop; 
	nop; 
	jalr x13, x6, 0; 
	bne x0, gp, fail; 
2:
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b;

	#-------------------------------------------------------------
	# Test delay slot instructions not executed nor bypassed
	#-------------------------------------------------------------

	.option push
	.align 2
	.option norvc
test_7:
	li gp, 7; 
	li t0, 1; 
	la t1, 1f; 
	jr t1, -4; 
	addi t0, t0, 1; 
	addi t0, t0, 1; 
	addi t0, t0, 1; 
	addi t0, t0, 1; 
1:
addi t0, t0, 1; 
	addi t0, t0, 1;; 
	li x7, ((4) & ((1 << (32 - 1) << 1) - 1)); 
bne t0, x7, fail;

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
	
	
