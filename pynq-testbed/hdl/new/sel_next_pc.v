`timescale 1ns / 1ps
`include "defines.v"
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/20/2023 11:53:30 AM
// Design Name: 
// Module Name: sel_next_pc
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


module sel_next_pc(
    input [8:0] op,
    input sign,
    input cmp,
    input [31:0] pc,
    input [31:0] pc_add_4,
    input [31:0] pc_imm,
    input [31:0] op1_imm,
    output reg [31:0] next_pc
    );
    
    always @ *
    begin
        case(op)
            (`IJ): next_pc = op1_imm;
            (`B):  next_pc = (cmp == 1'b1) ? pc_imm : pc_add_4;
            (`J):  next_pc = pc_imm;
            (`I2): next_pc = (sign == 1'b0) ? pc : pc_add_4;
            (`S2): next_pc = (sign == 1'b0) ? pc : pc_add_4;
            default: next_pc = pc_add_4;
        endcase
    end
endmodule
