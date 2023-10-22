`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/19/2023 02:24:09 PM
// Design Name: 
// Module Name: 
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

//one-hot encoding for op type
`define MRI 9'b000000001 // merged R and I op
`define IJ  9'b000000010
`define I2  9'b000000100
`define S1  9'b000001000
`define S2  9'b000010000
`define B   9'b000100000
`define U   9'b001000000
`define J   9'b010000000
`define NA  9'b100000000
    
    //index of sub-op type
`define OP0 10'b0000000001 //ADD, JALR, LB, SB, BEQ, LUI, JAL
`define OP1 10'b0000000010 //SLL, LH, SH, BNE, AUIPC
`define OP2 10'b0000000100 //SLT, LW, SW
`define OP3 10'b0000001000 //SLTU
`define OP4 10'b0000010000 //XOR, LBU, BLT
`define OP5 10'b0000100000 //SRL, LHU, BGE
`define OP6 10'b0001000000 //OR, BLTU
`define OP7 10'b0010000000 //AND, BGEU
`define OP8 10'b0100000000 //SUB
`define OP9 10'b1000000000 //SRA
    
//RR/RI op
`define RR 2'b01
`define RI 2'b10