	.section .text.entry
	.globl _start

_start:
test_2:
	li gp, 2; 
	.align 3; 
	lla a0, 1f + 10000; 
	jal a1, 1f; 
1:
	sub a0, a0, a1;; 
	li x7, ((10000) & ((1 << (32 - 1) << 1) - 1)); 
	bne a0, x7, fail;






test_3:
	li gp, 3; 
	.align 3; 
	lla a0, 1f - 10000; 
	jal a1, 1f; 
1:
sub a0, a0, a1;; 
li x7, ((-10000) & ((1 << (32 - 1) << 1) - 1)); 
bne a0, x7, fail;

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
	
	
