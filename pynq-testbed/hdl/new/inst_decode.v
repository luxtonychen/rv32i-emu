`timescale 1ns / 1ps
`include "defines.v"

//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/18/2023 02:38:23 PM
// Design Name: 
// Module Name: inst_decode
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


module inst_decode(
    input [31:0] mem_data,
    output reg [20:0] opc,
    output [4:0] rs1,
    output [4:0] rs2,
    output [4:0] rd,
    output reg [31:0] imm
    );
    
    assign rs1 = mem_data[19:15];
    assign rs2 = mem_data[24:20];
    assign rd  = mem_data[11:7];
    
    wire [6:0]  opcode = mem_data[6:0]; 
    wire [2:0]  func3  = mem_data[14:12];
    wire [6:0]  func7  = mem_data[31:25];
    wire [31:0] imm_i  = {{20{mem_data[31]}}, mem_data[31:20]};
    wire [31:0] imm_s  = {{20{mem_data[31]}}, func7, rd};
    wire [31:0] imm_b  = {{19{mem_data[31]}}, mem_data[31], mem_data[7], mem_data[30:25], mem_data[11:8], 1'b0};
    wire [31:0] imm_u  = {mem_data[31:12], 12'b0};
    wire [31:0] imm_j  = {{11{mem_data[31]}}, mem_data[31], mem_data[19:12], mem_data[20], mem_data[30:21], 1'b0};
    
    always @ (*) 
    begin
        case(opcode)
            (7'b0110011): begin //R Inst
                case(func3)
                    (3'h0):  begin
                        case(func7)
                            (7'h00): begin
                                opc = {`MRI, `OP0, `RR}; 
                                imm = 32'b0;
                            end
                            (7'h20): begin
                                opc = {`MRI, `OP8, `RR};
                                imm = 32'b0;
                            end
                            default: begin
                                opc = {`NA, 12'b0};
                                imm = 32'b0;
                            end 
                        endcase
                     end
                    (3'h1): begin
                        opc = {`MRI, `OP1,`RR};
                        imm = 32'b0;
                     end
                    (3'h2): begin
                        opc = {`MRI, `OP2, `RR};
                        imm = 32'b0;
                     end
                    (3'h3): begin
                        opc = {`MRI, `OP3, `RR};
                        imm = 32'b0;
                     end
                    (3'h4): begin
                        opc = {`MRI, `OP4, `RR};
                        imm = 32'b0;
                     end
                    (3'h5): begin
                        case(func7)
                            (7'h00): begin
                                opc = {`MRI, `OP5, `RR};
                                imm = 32'b0;
                            end
                            (7'h20): begin
                                opc = {`MRI, `OP9, `RR};
                                imm = 32'b0;
                            end
                            default: begin
                                opc = {`NA, 12'b0};
                                imm = 32'b0;
                            end 
                        endcase
                     end
                    (3'h6): begin
                        opc = {`MRI, `OP6, `RR};
                        imm = 32'b0;
                     end
                    (3'h7): begin
                        opc = {`MRI, `OP7, `RR};
                        imm = 32'b0;
                     end
                    default:  begin
                        opc = {`NA, 12'b0};
                        imm = 32'b0;
                    end
                endcase
             end 
            (7'b0010011): begin //I Inst
                case(func3)
                    (3'h0):  begin
                        opc = {`MRI, `OP0, `RI};
                        imm = imm_i;
                     end
                    (3'h1): begin
                        opc = {`MRI, `OP1, `RI};
                        imm = imm_i;
                     end
                    (3'h2): begin
                        opc = {`MRI, `OP2, `RI};
                        imm = imm_i;
                     end
                    (3'h3): begin
                        opc = {`MRI, `OP3, `RI};
                        imm = imm_i;
                     end
                    (3'h4): begin
                        opc = {`MRI, `OP4, `RI};
                        imm = imm_i;
                     end
                    (3'h5): begin
                        case(func7)
                            (7'h00): begin
                                opc = {`MRI, `OP5, `RI};
                                imm = imm_i;
                            end
                            (7'h20): begin
                                opc = {`MRI, `OP9, `RI};
                                imm = imm_i;
                            end
                            default: begin
                                opc = {`NA, 12'b0};
                                imm = 32'b0;
                            end 
                        endcase
                     end
                    (3'h6): begin
                        opc = {`MRI, `OP6, `RI};
                        imm = imm_i;
                     end
                    (3'h7): begin
                        opc = {`MRI, `OP7, `RI};
                        imm = imm_i;
                     end
                    default:  begin
                        opc = {`NA, 12'b0};
                        imm = 32'b0;
                    end
                endcase
            end
            (7'b0000011): begin //L Inst
                case(func3)
                    (3'h0): begin
                        opc = {`I2, `OP0, 2'b01};
                        imm = imm_i;
                     end
                    (3'h1): begin
                        opc = {`I2, `OP1, 2'b01};
                        imm = imm_i;
                     end
                    (3'h2): begin
                        opc = {`I2, `OP2, 2'b01};
                        imm = imm_i;
                     end
                    (3'h4): begin
                        opc = {`I2, `OP4, 2'b01};
                        imm = imm_i;
                     end
                    (3'h5): begin
                        opc = {`I2, `OP5, 2'b01};
                        imm = imm_i;
                     end
                    default: begin
                        opc = {`NA, 12'b0};
                        imm = 32'b0;
                    end
                endcase
            end
            (7'b0100011): begin //S Inst
                case(func3)
                    (3'h0): begin
                        opc = {`S2, `OP0, 2'b01};
                        imm = imm_s;
                     end
                    (3'h1): begin
                        opc = {`S2, `OP1, 2'b01};
                        imm = imm_s;
                     end
                    (3'h2): begin
                        opc = {`S1, `OP2, 2'b01};
                        imm = imm_s;
                     end
                    default: begin
                        opc = {`NA, 12'b0};
                        imm = 32'b0;
                    end
                endcase
            end
            (7'b1100011): begin //B Inst
                case(func3)
                    (3'h0): begin
                        opc = {`B, `OP0, 2'b01};
                        imm = imm_b;
                     end
                    (3'h1): begin
                        opc = {`B, `OP1, 2'b01};
                        imm = imm_b;
                    end
                    (3'h4): begin
                        opc = {`B, `OP4, 2'b01};
                        imm = imm_b;
                    end
                    (3'h5): begin
                        opc = {`B, `OP5, 2'b01};
                        imm = imm_b;
                    end
                    (3'h6): begin
                        opc = {`B, `OP6, 2'b01};
                        imm = imm_b;
                    end
                    (3'h7): begin
                        opc = {`B, `OP7, 2'b01};
                        imm = imm_b;
                    end
                    default: begin
                        opc = {`NA, 12'b0};
                        imm = 32'b0;
                    end
                endcase
            end
            (7'b1101111): begin //JAL
                opc = {`J, `OP0, 2'b00};
                imm = imm_j;
            end
            (7'b1100111): begin //JALR
                opc = {`IJ, `OP0, 2'b00};
                imm = imm_i;
            end
            (7'b0110111): begin //LUI
                opc = {`U, `OP0, 2'b00};
                imm = imm_u;
            end
            (7'b0010111): begin //AUIPC
                opc = {`U, `OP1, 2'b00};
                imm = imm_u;
            end
            default: begin
                opc = {`NA, 12'b0};
                imm = 32'b0;
            end
        endcase
    end
endmodule