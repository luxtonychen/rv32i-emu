`timescale 1ns / 1ps
`include "defines.v"
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/20/2023 10:42:17 AM
// Design Name: 
// Module Name: get_mem_data_r
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


module get_mem_data_r(
    input [18:0] opc,
    input [31:0] mem_data,
    output reg [31:0] i2_r_data
    );
    
    wire [31:0] mem_data_sb = {{24{mem_data[7]}}, mem_data[7:0]};
    wire [31:0] mem_data_sh = {{16{mem_data[15]}}, mem_data[15:0]};
    wire [31:0] mem_data_ub = {24'b0, mem_data[7:0]};
    wire [31:0] mem_data_uh = {16'b0, mem_data[15:0]};
    
    always @ *
    begin
        case(opc)
            {`I2, `OP0}: i2_r_data = mem_data_sb;
            {`I2, `OP1}: i2_r_data = mem_data_sh;
            {`I2, `OP4}: i2_r_data = mem_data_ub;
            {`I2, `OP5}: i2_r_data = mem_data_uh;
            default: i2_r_data = mem_data;
        endcase
    end
endmodule
