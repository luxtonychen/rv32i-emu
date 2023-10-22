`timescale 1ns / 1ps
`include "defines.v"
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/20/2023 11:00:14 AM
// Design Name: 
// Module Name: sel_reg_res
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


module sel_reg_res(
    input [8:0] op,
    input [31:0] a_res,
    input [31:0] i2_r_data,
    input [31:0] pc_add_4,
    input [31:0] res_upper_imm,
    output reg [31:0] res
    );
    
    always @ *
    begin
        case(op)
            (`MRI): res = a_res;
            (`IJ):  res = pc_add_4;
            (`I2):  res = i2_r_data;
            (`U):   res = res_upper_imm;
            (`J):   res = pc_add_4;
            default: res = a_res;
        endcase
    end
endmodule
