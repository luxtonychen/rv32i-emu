`timescale 1ns / 1ps
`include "defines.v"
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/19/2023 05:29:18 PM
// Design Name: 
// Module Name: comparator
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


module comparator(
    input [9:0] opc,
    input [31:0] op1,
    input [31:0] op2,
    output reg res
    );
    
    always @ *
    begin
        case(opc)
            (`OP1): res = (op1 != op2)                   ? 1'b1 : 1'b0;
            (`OP4): res = ($signed(op1) < $signed(op2))  ? 1'b1 : 1'b0;
            (`OP5): res = ($signed(op1) >= $signed(op2)) ? 1'b1 : 1'b0;
            (`OP6): res = (op1 < op2)                    ? 1'b1 : 1'b0;
            (`OP7): res = (op1 >= op2)                   ? 1'b1 : 1'b0;
            default: res = (op1 == op2)                  ? 1'b1 : 1'b0;
        endcase
    end
endmodule
