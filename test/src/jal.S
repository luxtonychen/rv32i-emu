	.section .text.entry
	.globl _start

_start:
	#-------------------------------------------------------------
	# Test 2:	Basic test
	#-------------------------------------------------------------

test_2:
	li gp, 2
	li ra, 0

	jal x4, target_2
linkaddr_2:
	nop
	nop

	j fail

target_2:
	la x2, linkaddr_2
	bne x2, x4, fail

	#-------------------------------------------------------------
	# Test delay slot instructions not executed nor bypassed
	#-------------------------------------------------------------

test_3:
	li gp, 3; 
	li ra, 1; 
	jal x0, 1f; 
	addi ra, ra, 1; 
	addi ra, ra, 1; 
	addi ra, ra, 1; 
	addi ra, ra, 1; 
1:
	addi ra, ra, 1; 
	addi ra, ra, 1;; 
	li x7, ((3) & ((1 << (32 - 1) << 1) - 1)); 
	bne ra, x7, fail;

	
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
	
	
