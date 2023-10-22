`timescale 1ns / 1ps
`include "defines.v"
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/19/2023 02:58:15 PM
// Design Name: 
// Module Name: arith
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


module arith(
    input [9:0] aop,
    input [1:0] rr_ri,
    input [31:0] op1,
    input [31:0] op2_1,
    input [31:0] imm,
    output [31:0] a_res
    );
    
    wire [31:0] op2 = (rr_ri == `RR) ? op2_1 : imm;
    wire [31:0] s_op1_lt_op2 = ($signed(op1) < $signed(op2)) ? 32'b1 : 32'b0;
    //wire [31:0] s_op1_ge_op2 = ($signed(op1) >= $signed(op2)) ? 32'b1 : 32'b0;
    wire [31:0] u_op1_lt_op2 = (op1 < op2) ? 32'b1 : 32'b0;
    //wire [31:0] u_op1_ge_op2 = (op1 >= op2) ? 32'b1 : 32'b0;
    //wire [31:0] op1_eq_op2   = (op1 == op2) ? 32'b1 : 32'b0;
    
    reg [32:0] res;
    assign a_res = res[31:0];
    
    always @ * 
    begin
        case(aop)
            (`OP0): res = op1 + op2;
            (`OP1): res = {1'b0, op1 << op2[4:0]};
            (`OP2): res = {1'b0, s_op1_lt_op2};
            (`OP3): res = {1'b0, u_op1_lt_op2};
            (`OP4): res = {1'b0, op1 ^ op2};
            (`OP5): res = {1'b0, op1 >> op2[4:0]};
            (`OP6): res = {1'b0, op1 | op2};
            (`OP7): res = {1'b0, op1 & op2};
            (`OP8): res = {1'b0, op1 - op2};
            (`OP9): res = {1'b0, op1 >> op2[4:0]};
            default: res = op1 + op2;
        endcase
    end
endmodule
