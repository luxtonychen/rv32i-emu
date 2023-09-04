	.section .text.entry
	.globl _start

_start:
test_2:
	li gp, 2;
	li x1, ((0x00000000) & ((1 << (32 - 1) << 1) - 1));
	li x2, ((0x00000000) & ((1 << (32 - 1) << 1) - 1));
	add x14, x1, x2;
	li x7, ((0x00000000) & ((1 << (32 - 1) << 1) - 1));
	bne x14, x7, fail;
test_3:
	li gp, 3;
	li x1, ((0x00000001) & ((1 << (32 - 1) << 1) - 1));
	li x2, ((0x00000001) & ((1 << (32 - 1) << 1) - 1));
	add x14, x1, x2;
	li x7, ((0x00000002) & ((1 << (32 - 1) << 1) - 1));
	bne x14, x7, fail;
test_4:
	li gp, 4;
	li x1, ((0x00000003) & ((1 << (32 - 1) << 1) - 1));
	li x2, ((0x00000007) & ((1 << (32 - 1) << 1) - 1));
	add x14, x1, x2;;
	li x7, ((0x0000000a) & ((1 << (32 - 1) << 1) - 1));
	bne x14, x7, fail;;

test_5:
	li gp, 5;
	li x1, ((0x0000000000000000) & ((1 << (32 - 1) << 1) - 1));
	li x2, ((0xffffffffffff8000) & ((1 << (32 - 1) << 1) - 1));
	add x14, x1, x2;
	li x7, ((0xffffffffffff8000) & ((1 << (32 - 1) << 1) - 1));
	bne x14, x7, fail;;
test_6:
	li gp, 6;
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1));
	li x2, ((0x00000000) & ((1 << (32 - 1) << 1) - 1));
	add x14, x1, x2;;
	li x7, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1));
	bne x14, x7, fail;;
test_7: 
	li gp, 7;
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1));
	li x2, ((0xffffffffffff8000) & ((1 << (32 - 1) << 1) - 1));
	add x14, x1, x2;;
	li x7, ((0xffffffff7fff8000) & ((1 << (32 - 1) << 1) - 1));
	bne x14, x7, fail;;

test_8: 
	li gp, 8;
	li x1, ((0x0000000000000000) & ((1 << (32 - 1) << 1) - 1));
	li x2, ((0x0000000000007fff) & ((1 << (32 - 1) << 1) - 1));
	add x14, x1, x2;;
	li x7, ((0x0000000000007fff) & ((1 << (32 - 1) << 1) - 1));
	bne x14, x7, fail;;
test_9: 
	li gp, 9;
	li x1, ((0x000000007fffffff) & ((1 << (32 - 1) << 1) - 1));
	li x2, ((0x0000000000000000) & ((1 << (32 - 1) << 1) - 1));
	add x14, x1, x2;;
	li x7, ((0x000000007fffffff) & ((1 << (32 - 1) << 1) - 1));
	bne x14, x7, fail;;
test_10: 
	li gp, 10;
	li x1, ((0x000000007fffffff) & ((1 << (32 - 1) << 1) - 1));
	li x2, ((0x0000000000007fff) & ((1 << (32 - 1) << 1) - 1));
	add x14, x1, x2;;
	li x7, ((0x0000000080007ffe) & ((1 << (32 - 1) << 1) - 1));
	bne x14, x7, fail;;

test_11: 
	li gp, 11;
	li x1, ((0xffffffff80000000) & ((1 << (32 - 1) << 1) - 1));
	li x2, ((0x0000000000007fff) & ((1 << (32 - 1) << 1) - 1));
	add x14, x1, x2;;
	li x7, ((0xffffffff80007fff) & ((1 << (32 - 1) << 1) - 1));
	bne x14, x7, fail;;
test_12: 
	li gp, 12;
	li x1, ((0x000000007fffffff) & ((1 << (32 - 1) << 1) - 1));
	li x2, ((0xffffffffffff8000) & ((1 << (32 - 1) << 1) - 1));
	add x14, x1, x2;;
	li x7, ((0x000000007fff7fff) & ((1 << (32 - 1) << 1) - 1));
	bne x14, x7, fail;;

test_13: 
	li gp, 13;
	li x1, ((0x0000000000000000) & ((1 << (32 - 1) << 1) - 1));
	li x2, ((0xffffffffffffffff) & ((1 << (32 - 1) << 1) - 1));
	add x14, x1, x2;;
	li x7, ((0xffffffffffffffff) & ((1 << (32 - 1) << 1) - 1));
	bne x14, x7, fail;;
test_14: 
	li gp, 14;
	li x1, ((0xffffffffffffffff) & ((1 << (32 - 1) << 1) - 1));
	li x2, ((0x0000000000000001) & ((1 << (32 - 1) << 1) - 1));
	add x14, x1, x2;;
	li x7, ((0x0000000000000000) & ((1 << (32 - 1) << 1) - 1));
	bne x14, x7, fail;;
test_15: 
	li gp, 15;
	li x1, ((0xffffffffffffffff) & ((1 << (32 - 1) << 1) - 1));
	li x2, ((0xffffffffffffffff) & ((1 << (32 - 1) << 1) - 1));
	add x14, x1, x2;;
	li x7, ((0xfffffffffffffffe) & ((1 << (32 - 1) << 1) - 1));
	bne x14, x7, fail;;

test_16: 
	li gp, 16;
	li x1, ((0x0000000000000001) & ((1 << (32 - 1) << 1) - 1));
	li x2, ((0x000000007fffffff) & ((1 << (32 - 1) << 1) - 1));
	add x14, x1, x2;;
	li x7, ((0x0000000080000000) & ((1 << (32 - 1) << 1) - 1));
	bne x14, x7, fail;;

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
	
	
