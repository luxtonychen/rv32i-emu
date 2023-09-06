	.section .text.entry
	.globl _start

_start:

test_2: 
	li gp, 2; 
	lui x1, 0x00000; 
	li x7, ((0x0000000000000000) & ((1 << (32 - 1) << 1) - 1)); 
	bne x1, x7, fail;;
test_3: 
	li gp, 3; 
	lui x1, 0xfffff;sra x1,x1,1; 
	li x7, ((0xfffffffffffff800) & ((1 << (32 - 1) << 1) - 1)); 
	bne x1, x7, fail;;
test_4: 
	li gp, 4; 
	lui x1, 0x7ffff;sra x1,x1,20; 
	li x7, ((0x00000000000007ff) & ((1 << (32 - 1) << 1) - 1)); 
	bne x1, x7, fail;;
test_5: 
	li gp, 5; 
	lui x1, 0x80000;sra x1,x1,20; 
	li x7, ((0xfffffffffffff800) & ((1 << (32 - 1) << 1) - 1)); 
	bne x1, x7, fail;;

test_6: 
	li gp, 6; 

	lui x0, 0x80000; 

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
	.space 256 * 4
	.global data_end
data_end:	
