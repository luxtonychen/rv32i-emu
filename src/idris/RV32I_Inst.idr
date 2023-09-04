module RV32I_Inst

import BitsVec

public export
data ROP = ADD | SUB | XOR | OR | AND | SLL | SRL | SRA | SLT | SLTU

Show ROP where
  show ADD  = "ADD  " 
  show SUB  = "SUB  " 
  show XOR  = "XOR  " 
  show OR   = "OR   " 
  show AND  = "AND  " 
  show SLL  = "SLL  " 
  show SRL  = "SRL  " 
  show SRA  = "SRA  " 
  show SLT  = "SLT  " 
  show SLTU = "SLTU " 

public export
data IOP = ADDI | XORI | ORI | ANDI | SLLI | SRLI | SRAI | SLTI | SLTIU | LB | LH | LW | LBU | LHU | JALR

Show IOP where 
  show ADDI  = "ADDI "
  show XORI  = "XORI "
  show ORI   = "ORI  "
  show ANDI  = "ANDI "
  show SLLI  = "SLLI "
  show SRLI  = "SRLI "
  show SRAI  = "SRAI "
  show SLTI  = "SLTI "
  show SLTIU = "SLTIU"
  show LB    = "LB   "
  show LH    = "LH   "
  show LW    = "LW   "
  show LBU   = "LBU  "
  show LHU   = "LHU  "
  show JALR  = "JALR "

public export
data SOP = SB | SH | SW

Show SOP where
  show SB = "SB   "
  show SH = "SH   "
  show SW = "SW   "

public export
data BOP = BEQ | BNE | BLT | BGE | BLTU | BGEU

Show BOP where
  show BEQ  = "BEQ  "
  show BNE  = "BNE  "
  show BLT  = "BLT  "
  show BGE  = "BGE  "
  show BLTU = "BLTU "
  show BGEU = "BGEU "

public export
data UOP = LUI | AUIPC

Show UOP where
  show LUI = "LUI  "
  show AUIPC = "AUIPC"

public export
data JOP = JAL 

Show JOP where
  show JAL = "JAL  "

public export
data Inst : Type where
  R : (op:ROP) -> (rs1:BitsVec) -> (rs2:BitsVec) -> (rd:BitsVec)  -> Inst
  I : (op:IOP) -> (rs1:BitsVec) -> (imm:BitsVec) -> (rd:BitsVec)  -> Inst
  S : (op:SOP) -> (rs1:BitsVec) -> (rs2:BitsVec) -> (imm:BitsVec) -> Inst
  B : (op:BOP) -> (rs1:BitsVec) -> (rs2:BitsVec) -> (imm:BitsVec) -> Inst
  U : (op:UOP) -> (imm:BitsVec) -> (rd:BitsVec)  -> Inst
  J : (op:JOP) -> (imm:BitsVec) -> (rd:BitsVec)  -> Inst
  NA : Inst -- not valid

public export  
Show Inst where
  show (R op rs1 rs2 rd) = (show op) ++ " x" ++ (show rs1) ++ " x" ++ (show rs2) ++ " x" ++ (show rd)
  show (I op rs1 imm rd) = (show op) ++ " x" ++ (show rs1) ++ " #" ++ (show imm) ++ " x" ++ (show rd)
  show (S op rs1 rs2 imm) = (show op) ++ " M[x" ++ (show rs1) ++ " + #" ++ (show imm) ++ "] x" ++ (show rs2)
  show (B op rs1 rs2 imm) = (show op) ++ " x" ++ (show rs1) ++ " x" ++ (show rs2) ++ " #" ++ (show imm)
  show (U op imm rd) = (show op) ++ " x" ++ (show rd) ++ " #" ++ (show imm)
  show (J op imm rd) = (show op) ++ " x" ++ (show rd) ++ " #" ++ (show imm)
  show NA = "NA"


data OpCode' = R' | I' | L' | S' | B' | U1 | U2 | J1 | J2 | NA'

get_op_code : BitsVec -> OpCode'
get_op_code (MkBitsVec 7 0x33) = R' --Opcode 0110011
get_op_code (MkBitsVec 7 0x13) = I' --Opcode 0010011 
get_op_code (MkBitsVec 7 0x03) = L' --Opcode 0000011
get_op_code (MkBitsVec 7 0x23) = S' --Opcode 0100011
get_op_code (MkBitsVec 7 0x63) = B' --Opcode 1100011
get_op_code (MkBitsVec 7 0x6F) = J1 --Opcode 1101111
get_op_code (MkBitsVec 7 0x67) = J2 --Opcode 1100111
get_op_code (MkBitsVec 7 0x37) = U1 --Opcode 0110111
get_op_code (MkBitsVec 7 0x17) = U2 --Opcode 0010111
get_op_code _ = NA'


bv_compose_4 : (Bits8, Bits8) -> (Bits8, Bits8) -> (Bits8, Bits8) -> (Bits8, Bits8) 
            -> BitsVec -> BitsVec
bv_compose_4 (l1, h1) (l2, h2) (l3, h3) (l4, h4) bv = 
  bv_concatenate (bv_get_range l1 h1 bv) 
                 (bv_concatenate (bv_get_range l2 h2 bv) 
                                 (bv_concatenate (bv_get_range l3 h3 bv) 
                                                 (bv_get_range l4 h4 bv)))
public export
decode : BitsVec -> Inst
decode bv = 
  let b_0_6   = bv_get_range 0  7  bv
      b_7_11  = bv_get_range 7  12 bv
      b_12_14 = bv_get_range 12 15 bv
      b_15_19 = bv_get_range 15 20 bv
      b_20_24 = bv_get_range 20 25 bv
      b_25_31 = bv_get_range 25 32 bv
      opcode  = get_op_code b_0_6
  in case opcode of
          R' => case b_12_14 of
                    (MkBitsVec 3 0x0) => case b_25_31 of 
                                             (MkBitsVec 7 0x00) => R ADD b_15_19 b_20_24 b_7_11
                                             (MkBitsVec 7 0x20) => R SUB b_15_19 b_20_24 b_7_11
                                             _ => NA
                    (MkBitsVec 3 0x1) => R SLL  b_15_19 b_20_24 b_7_11
                    (MkBitsVec 3 0x2) => R SLT  b_15_19 b_20_24 b_7_11
                    (MkBitsVec 3 0x3) => R SLTU b_15_19 b_20_24 b_7_11
                    (MkBitsVec 3 0x4) => R XOR  b_15_19 b_20_24 b_7_11
                    (MkBitsVec 3 0x5) => case b_25_31 of 
                                              (MkBitsVec 7 0x00) => R SRL b_15_19 b_20_24 b_7_11
                                              (MkBitsVec 7 0x20) => R SRA b_15_19 b_20_24 b_7_11
                                              _ => NA
                    (MkBitsVec 3 0x6) => R OR  b_15_19 b_20_24 b_7_11
                    (MkBitsVec 3 0x7) => R AND b_15_19 b_20_24 b_7_11
                    _ => NA
          I' => let imm = bv_concatenate b_25_31 b_20_24 
                in case b_12_14 of
                       (MkBitsVec 3 0x0) => I ADDI b_15_19 imm b_7_11
                       (MkBitsVec 3 0x1) => I SLLI b_15_19 imm b_7_11
                       (MkBitsVec 3 0x2) => I SLTI b_15_19 imm b_7_11
                       (MkBitsVec 3 0x3) => I SLTIU b_15_19 imm b_7_11
                       (MkBitsVec 3 0x4) => I XORI b_15_19 imm b_7_11
                       (MkBitsVec 3 0x5) => case b_25_31 of 
                                                 (MkBitsVec 7 0x00) => I SRLI b_15_19 imm b_7_11
                                                 (MkBitsVec 7 0x20) => I SRAI b_15_19 imm b_7_11
                                                 _ => NA
                       (MkBitsVec 3 0x6) => I ORI b_15_19 imm b_7_11
                       (MkBitsVec 3 0x7) => I ANDI b_15_19 imm b_7_11
                       _ => NA
          L' => let imm = bv_concatenate b_25_31 b_20_24 
                in case b_12_14 of
                       (MkBitsVec 3 0x0) => I LB  b_15_19 imm b_7_11
                       (MkBitsVec 3 0x1) => I LH  b_15_19 imm b_7_11
                       (MkBitsVec 3 0x2) => I LW  b_15_19 imm b_7_11
                       (MkBitsVec 3 0x4) => I LBU b_15_19 imm b_7_11
                       (MkBitsVec 3 0x5) => I LHU b_15_19 imm b_7_11
                       _ => NA
          S' => let imm = bv_concatenate b_25_31 b_7_11 
                in case b_12_14 of
                       (MkBitsVec 3 0x0) => S SB b_15_19 b_20_24 imm
                       (MkBitsVec 3 0x1) => S SH b_15_19 b_20_24 imm
                       (MkBitsVec 3 0x2) => S SW b_15_19 b_20_24 imm
                       _ => NA
          B' => let imm = (bv_concatenate (bv_compose_4 (31, 32) (7, 8) (25, 31) (8, 12) bv)
                                          (MkBitsVec 1 0))
               in case b_12_14 of
                    (MkBitsVec 3 0x0) => B BEQ  b_15_19 b_20_24 imm
                    (MkBitsVec 3 0x1) => B BNE  b_15_19 b_20_24 imm
                    (MkBitsVec 3 0x4) => B BLT  b_15_19 b_20_24 imm
                    (MkBitsVec 3 0x5) => B BGE  b_15_19 b_20_24 imm
                    (MkBitsVec 3 0x6) => B BLTU b_15_19 b_20_24 imm
                    (MkBitsVec 3 0x7) => B BGEU b_15_19 b_20_24 imm
                    _ => NA
          J1 => J JAL (bv_concatenate (bv_compose_4 (31, 32) (12, 20) (20, 21) (21, 31) bv) 
                                      (MkBitsVec 1 0)) b_7_11
          J2 => I JALR b_15_19 (bv_get_range 20 32 bv) b_7_11
          U1 => U LUI (bv_get_range 12 32 bv) b_7_11
          U2 => U AUIPC (bv_get_range 12 32 bv) b_7_11
          _ => NA
