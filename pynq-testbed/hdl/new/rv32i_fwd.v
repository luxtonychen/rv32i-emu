`timescale 1ns / 1ps
`include "defines.v"
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/18/2023 01:53:20 PM
// Design Name: 
// Module Name: rv32i_fwd
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


module rv32i_fwd(
    input [31:0] mem_data,
    input [31:0] raddr,
    input clk,
    input rst_n,
    output [31:0] waddr,
    output [31:0] wdata,
    output wen,
    output [31:0] raddr_next,
    output reg state
    );
    
    reg sign;
    reg [4:0] reg_idx;
    reg [20:0] saved_opc; // [20:12 op | 11:2 sub_op | 1:0 RR/RI] one-hot
    reg [31:0] saved_pc;
       
    
    wire [20:0] opc_1;
    wire [4:0]  rs1;
    wire [4:0]  rs2_1;
    wire [4:0]  rd_1;
    wire [31:0] imm;
    
    inst_decode decode (
        .mem_data(mem_data),
        .opc(opc_1),
        .rs1(rs1),
        .rs2(rs2_1),
        .rd(rd_1),
        .imm(imm)
    );
    
    wire [4:0] rs2 = (sign == 1'b1) ? reg_idx : rs2_1;
    wire [4:0] rd  = (sign == 1'b1) ? reg_idx : rd_1;
    
    wire [31:0] res;
    wire [31:0] op1;
    wire [31:0] op2;
    wire regf_we;
    
    regisetr_file regf (
        .raddr1(rs1),
        .raddr2(rs2),
        .waddr(rd),
        .wdata(res),
        .clk(clk),
        .we(regf_we),
        .rdata1(op1),
        .rdata2(op2)
    );
    
    wire [31:0] pc  = (sign == 1'b1) ? saved_pc  : raddr;
    wire [20:0] opc = (sign == 1'b1) ? saved_opc : opc_1;
    
    wire [8:0]  op     = opc[20:12];
    wire [9:0]  sub_op = opc[11: 2];
    wire [1:0]  rr_ri  = opc[ 1: 0];
    
    wire [31:0] pc_add_4 = pc + 32'd4;
    
    wire [32:0] pc_imm_   = pc + imm;
    wire [31:0] pc_imm = pc_imm_[31:0];
    
    wire [32:0] op1_imm_  = op1 + imm;
    wire [31:0] op1_imm  = op1_imm_[31:0];
    
    wire [31:0] a_res;
    
    arith alu (
        .aop(sub_op),
        .rr_ri(rr_ri),
        .op1(op1),
        .op2_1(op2),
        .imm(imm),
        .a_res(a_res)
    );
    
    wire [31:0] res_upper_imm = (opc[20:2] == {`U, `OP0}) ? imm : pc_imm;
    wire cmp;
    
    comparator cmp_fn(
        .opc(sub_op),
        .op1(op1),
        .op2(op2),
        .res(cmp)
    );
    
    wire [31:0] data_h = {mem_data[31:16], op2[15:0]};
    wire [31:0] data_b = {mem_data[31:8], op2[7:0]};
    wire [31:0] s2_w_data = ({op, sub_op} == {`S2, `OP1}) ? data_h : data_b;
    
    wire [31:0] i2_r_data;
    
    get_mem_data_r get_r_data(
        .opc({op, sub_op}),
        .mem_data(mem_data),
        .i2_r_data(i2_r_data)
    );
    
    sel_reg_res sel_reg_res_0 (
        .op(op),
        .a_res(a_res),
        .i2_r_data(i2_r_data),
        .pc_add_4(pc_add_4),
        .res_upper_imm(res_upper_imm),
        .res(res)
    );
    
    wire [31:0] next_pc;
    
    sel_next_pc sel_next_pc_0(
        .op(op),
        .sign(sign),
        .cmp(cmp),
        .pc(pc),
        .pc_add_4(pc_add_4),
        .pc_imm(pc_imm),
        .op1_imm(op1_imm),
        .next_pc(next_pc)
    );
    
    assign waddr = (op == `S1) ? op1_imm : raddr;
    assign wdata = (op == `S2) ? s2_w_data : op2;
    assign wen = (op == `S1 && sign == 1'b0) || (op == `S2 && sign == 1'b1) ? 1'b1 : 1'b0; 
    assign raddr_next = (op == `S2 || op == `I2) && (sign == 1'b0) ? op1_imm : next_pc;
    assign regf_we = (sign == 1'b0 && op == `I2) || (op == `S2) || (op == `B) ? 1'b0 : 1'b1;
    
    always @ (posedge clk)
    begin
        if(!rst_n)
        begin
            sign      <= 1'b0;
            saved_opc <= 21'b0;
            saved_pc  <= 32'b0;
            reg_idx   <= 5'b0;
            state     <= 1'b0;
        end
        else
        begin
            sign      <= (op == `S2 || op == `I2) && (sign == 1'b0) ? 1'b1 : 1'b0;
            saved_opc <= opc;
            saved_pc  <= next_pc;
            reg_idx   <=  (sign == 1'b0 && op == `S2) ? rs2 : rd;
            state     <= ~state;
        end
    end
    
endmodule
