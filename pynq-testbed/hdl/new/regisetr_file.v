`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/18/2023 01:58:37 PM
// Design Name: 
// Module Name: regisetr_file
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


module regisetr_file(
    input [4:0] raddr1,
    input [4:0] raddr2,
    input [4:0] waddr,
    input [31:0] wdata,
    input we,
    input clk,
    output [31:0] rdata1,
    output [31:0] rdata2
    );
    
    wire [31:0] mem_1_dout;
    wire [31:0] mem_2_dout;
    
    regf_mem mem_1 (
        .a(waddr),        // input wire [4 : 0] a
        .d(wdata),        // input wire [31 : 0] d
        .dpra(raddr1),  // input wire [4 : 0] dpra
        .clk(clk),    // input wire clk
        .we(we),    // input wire we
        .dpo(mem_1_dout)    // output wire [31 : 0] dpo
        );
        
    regf_mem mem_2 (
        .a(waddr),        // input wire [4 : 0] a
        .d(wdata),        // input wire [31 : 0] d
        .dpra(raddr2),  // input wire [4 : 0] dpra
        .clk(clk),    // input wire clk
        .we(we),    // input wire we
        .dpo(mem_2_dout)    // output wire [31 : 0] dpo
        );
        
    assign rdata1 = (raddr1 == 5'd0) ? 32'd0 : mem_1_dout;
    assign rdata2 = (raddr2 == 5'd0) ? 32'd0 : mem_2_dout;
     
    
endmodule
