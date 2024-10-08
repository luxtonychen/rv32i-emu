	.section .text.entry
	.globl _start

_start:
	#-------------------------------------------------------------
	# Logical tests
	#-------------------------------------------------------------

test_2:
	li gp, 2; 
	li x1, ((0xff00ff00) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0x0f0f0f0f) & ((1 << (32 - 1) << 1) - 1)); 
	and x14, x1, x2;; 
	li x7, ((0x0f000f00) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_3:
	li gp, 3; 
	li x1, ((0x0ff00ff0) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0xf0f0f0f0) & ((1 << (32 - 1) << 1) - 1)); 
	and x14, x1, x2;; 
	li x7, ((0x00f000f0) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_4:
	li gp, 4; 
	li x1, ((0x00ff00ff) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0x0f0f0f0f) & ((1 << (32 - 1) << 1) - 1)); 
	and x14, x1, x2;; 
	li x7, ((0x000f000f) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_5:
	li gp, 5; 
	li x1, ((0xf00ff00f) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0xf0f0f0f0) & ((1 << (32 - 1) << 1) - 1)); 
	and x14, x1, x2;; 
	li x7, ((0xf000f000) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;

	#-------------------------------------------------------------
	# Source/Destination tests
	#-------------------------------------------------------------

test_6:
	li gp, 6; 
	li x1, ((0xff00ff00) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0x0f0f0f0f) & ((1 << (32 - 1) << 1) - 1)); 
	and x1, x1, x2;; 
	li x7, ((0x0f000f00) & ((1 << (32 - 1) << 1) - 1)); 
	bne x1, x7, fail;;
test_7:
	li gp, 7; 
	li x1, ((0x0ff00ff0) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0xf0f0f0f0) & ((1 << (32 - 1) << 1) - 1)); 
	and x2, x1, x2;; 
	li x7, ((0x00f000f0) & ((1 << (32 - 1) << 1) - 1)); 
	bne x2, x7, fail;;
test_8:
	li gp, 8; 
	li x1, ((0xff00ff00) & ((1 << (32 - 1) << 1) - 1)); 
	and x1, x1, x1;; 
	li x7, ((0xff00ff00) & ((1 << (32 - 1) << 1) - 1)); 
	bne x1, x7, fail;;

	#-------------------------------------------------------------
	# Bypassing tests
	#-------------------------------------------------------------

test_9:
	li gp, 9; 
	li x4, 0; 
1:
	li x1, ((0xff00ff00) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0x0f0f0f0f) & ((1 << (32 - 1) << 1) - 1)); 
	and x14, x1, x2; 
	addi x6, x14, 0; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0x0f000f00) & ((1 << (32 - 1) << 1) - 1)); 
	bne x6, x7, fail;;
test_10:
	li gp, 10; 
	li x4, 0; 
1:
	li x1, ((0x0ff00ff0) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0xf0f0f0f0) & ((1 << (32 - 1) << 1) - 1)); 
	and x14, x1, x2; 
	nop; 
	addi x6, x14, 0; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0x00f000f0) & ((1 << (32 - 1) << 1) - 1)); 
	bne x6, x7, fail;;
test_11:
	li gp, 11; 
	li x4, 0; 
1:
	li x1, ((0x00ff00ff) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0x0f0f0f0f) & ((1 << (32 - 1) << 1) - 1)); 
	and x14, x1, x2; 
	nop; 
	nop; 
	addi x6, x14, 0; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0x000f000f) & ((1 << (32 - 1) << 1) - 1)); 
	bne x6, x7, fail;;

test_12:
	li gp, 12; 
	li x4, 0; 
1:
	li x1, ((0xff00ff00) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0x0f0f0f0f) & ((1 << (32 - 1) << 1) - 1)); 
	and x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0x0f000f00) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_13:
	li gp, 13; 
	li x4, 0; 
1:
	li x1, ((0x0ff00ff0) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0xf0f0f0f0) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	and x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0x00f000f0) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_14:
	li gp, 14; 
	li x4, 0; 
1:
	li x1, ((0x00ff00ff) & ((1 << (32 - 1) << 1) - 1)); 
	li x2, ((0x0f0f0f0f) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	nop; 
	and x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0x000f000f) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_15:
	li gp, 15; 
	li x4, 0; 
1:
	li x1, ((0xff00ff00) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	li x2, ((0x0f0f0f0f) & ((1 << (32 - 1) << 1) - 1)); 
	and x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0x0f000f00) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_16:
	li gp, 16; 
	li x4, 0; 
1:
	li x1, ((0x0ff00ff0) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	li x2, ((0xf0f0f0f0) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	and x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0x00f000f0) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_17:
	li gp, 17; 
	li x4, 0; 
1:
	li x1, ((0x00ff00ff) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	nop; 
	li x2, ((0x0f0f0f0f) & ((1 << (32 - 1) << 1) - 1)); 
	and x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0x000f000f) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;

test_18:
	li gp, 18; 
	li x4, 0; 
1:
	li x2, ((0x0f0f0f0f) & ((1 << (32 - 1) << 1) - 1)); 
	li x1, ((0xff00ff00) & ((1 << (32 - 1) << 1) - 1)); 
	and x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0x0f000f00) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_19:
	li gp, 19; 
	li x4, 0; 
1:
	li x2, ((0xf0f0f0f0) & ((1 << (32 - 1) << 1) - 1)); 
	li x1, ((0x0ff00ff0) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	and x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0x00f000f0) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_20:
	li gp, 20; 
	li x4, 0; 
1:
	li x2, ((0x0f0f0f0f) & ((1 << (32 - 1) << 1) - 1)); 
	li x1, ((0x00ff00ff) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	nop; 
	and x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0x000f000f) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_21:
	li gp, 21; 
	li x4, 0; 
1:
	li x2, ((0x0f0f0f0f) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	li x1, ((0xff00ff00) & ((1 << (32 - 1) << 1) - 1)); 
	and x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0x0f000f00) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_22:
	li gp, 22; 
	li x4, 0; 
1:
	li x2, ((0xf0f0f0f0) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	li x1, ((0x0ff00ff0) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	and x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0x00f000f0) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;
test_23:
	li gp, 23; 
	li x4, 0; 
1:
	li x2, ((0x0f0f0f0f) & ((1 << (32 - 1) << 1) - 1)); 
	nop; 
	nop; 
	li x1, ((0x00ff00ff) & ((1 << (32 - 1) << 1) - 1)); 
	and x14, x1, x2; 
	addi x4, x4, 1; 
	li x5, 2; 
	bne x4, x5, 1b; 
	li x7, ((0x000f000f) & ((1 << (32 - 1) << 1) - 1)); 
	bne x14, x7, fail;;

test_24:
	li gp, 24; 
	li x1, ((0xff00ff00) & ((1 << (32 - 1) << 1) - 1)); 
	and x2, x0, x1;; 
	li x7, ((0) & ((1 << (32 - 1) << 1) - 1)); 
	bne x2, x7, fail;;
test_25:
	li gp, 25; 
	li x1, ((0x00ff00ff) & ((1 << (32 - 1) << 1) - 1)); 
	and x2, x1, x0;; 
	li x7, ((0) & ((1 << (32 - 1) << 1) - 1)); 
	bne x2, x7, fail;;
test_26:
	li gp, 26; 
	and x1, x0, x0;; 
	li x7, ((0) & ((1 << (32 - 1) << 1) - 1)); 
	bne x1, x7, fail;;
test_27:
li gp, 27; 
li x1, ((0x11111111) & ((1 << (32 - 1) << 1) - 1)); 
li x2, ((0x22222222) & ((1 << (32 - 1) << 1) - 1)); 
and x0, x1, x2;; 
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
	
	
