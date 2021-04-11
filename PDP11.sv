// PDP11.sv - ECE586 Final Project - PDP Simulator
//
// Meshal Albaiz
// Tapasya Bhatnagar
// Tristan Cunderla
// Ruben Maldonado
//
// Winter 2018
// 2/18/2019
//
// DESCRIPTION______________________________________________________________________________
//  Simulates PDP11 ISA -
//__________________________________________________________________________________________

module PDP11(

  input [19:0] input_in,
  input logic signed [31:0] count,
  output logic [17:0] output_out,
  output logic [15:0] reg0, reg1, reg2, reg3, reg4, reg5, reg6,
  output logic signed [15:0] reg7,
  output logic [3:0] NZVC,
  output string instruction_string,
  output string regd_string,
  output string regs_string,
  output logic [1:0] instruction_type,
  output logic [63:0] instruction_num,
  output logic B_flag,
  output logic J_flag,
  output logic signed [8:0]offset_temp,
  output logic signed [15:0] PC_temp
);

logic [15:0] memory [0:65535]; // memory space
logic [15:0] instruction; // 16 bit instruction
logic [3:0] sign_char; // sign character * @ -
logic B; // b bit, bit 16 of instruction
logic [1:0] next_instruction_flag = 2'b0; // flag for two-line instructions
logic signed [15:0] PC = 16'b0; // program counter
logic signed [15:0] PC_start = 16'b0; // starting address
logic [2:0] modeS, modeD, regS, regD; // mode source, mode destination, register source, register destination
logic signed [15:0] PC_read; // PC + 2 for double liner operations

logic signed [15:0] register [0:7]; // register array
logic N = 0;
logic Z_Flag = 0;
logic V = 0;
logic C = 0;
logic [2:0] opcodeD; // opcode for double operand
logic [8:0] opcodeS; // opcode for single operand
logic [7:0] opcodeB; // opcode for program control
logic signed [15:0] result, result_temp; // instruction result, result temp hold the value of operations that only affect flags
logic signed [15:0] valD, valS; // the value of the source and value of destination
logic [1:0] single_double_flag; // flag for single, double, and branch control instructions
logic [15:0] address; // address being accessed
logic signed [5:0] shift; // shift value for program control

logic signed [7:0] offset; // offset variable
logic [63:0] instruction_counter = 0; // instruction counter
logic signed [15:0] remainder; // remainder from division
logic signed [31:0] mul_result; // multiplication result
logic [15:0] old_instruction, second_instruction; // old and second instruction for two and three word instructions
logic B_bit; // b bit

always @(input_in  or count) begin
  B_flag = 1'b0; // set branch and jump flags to 0
  J_flag = 1'b0;
  instruction = input_in[15:0]; // get 16-bit instruction
  sign_char = input_in[19:16]; // get sign

  if(sign_char == 4'b0100) begin // if sign is @
    PC = instruction; // set PC to instruction
  end

  else if(sign_char == 4'b1000) begin // if sign is *
    PC_start = instruction; // set starting PC for executing instruction
  end

  else if(sign_char == 4'b0000 && PC < PC_start) begin // if input is data
    memory[PC] = instruction; // save data to memory
    PC = PC + 2;
  end

  else if(sign_char == 4'b0000 && PC >= PC_start) begin // if input is instruction
    memory[PC] = instruction; // save instruction to memory
    if(next_instruction_flag == 0) begin // if instruction was not preceded by a double or triple word instruction
      B = instruction[15]; // B bit
      if(instruction == 16'b0) begin // if instruction is halt
        output_out = {2'b10, PC};
        instruction_string = "HALT";
        instruction_counter = instruction_counter + 1; // add one to instruction count
      end

      else if(instruction[14:12] == 3'b000) begin

// ----------------------------------------------------------------------- SINGLE OPERAND

        if(instruction[11] == 1'b1 || instruction[14:6] == 9'b000000011) begin // if instruction is single operand
          opcodeS = instruction[14:6]; // get opcode
          modeD = instruction[5:3]; // get destination mode
          regD = instruction[2:0]; // get destination register
          single_double_flag = 1;  // set single flag on
          if(modeD == 3'h6 || modeD == 3'h7 || regD == 3'h7) begin // if instruction is a double word instruction
            next_instruction_flag = 1; // set double word instruction flag
            old_instruction = instruction; // save current instruction
            output_out = {2'b10, PC}; // output instruction fetch
            PC = PC + 2; // increment PC
          end

          else begin // if instruction is single word
          instruction_counter = instruction_counter + 1; // increment instruction count
          case(modeD) // destination mode
            3'b000: begin // register addressing mode
              valD = register[regD];
              $sformat(regd_string,"R%d", regD);
            end

            3'b001: begin // register deferred addressing mode
              address = register[regD];
              valD = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100;
              $sformat(regd_string,"(R%d)", regD);
            end

            3'b010: begin // auto-increment addressing mode
              address = register[regD];
              valD = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100
              $sformat(regd_string,"(R%d)+", regD);
            end

            3'b011: begin // auto-increment deferred addressing mode
              address = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100;
              valD = memory[memory[register[regD]]];
              output_out = {2'b0, memory[register[regD]]};
              #100
              $sformat(regd_string,"@(R%d)+", regD);
            end

            3'b100: begin // auto-decrement addressing mode
              address = register[regD];
              valD = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100;
              $sformat(regd_string,"-(R%d)", regD);
            end

            3'b101: begin // auto-decrement deferred addressing mode
              valD = memory[memory[register[regD]]];
              address = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100
              output_out = {2'b0, memory[register[regD]]};
              #100;
              $sformat(regd_string,"@-(R%d)", regD);
            end
          endcase

          if(instruction[14:6] == 9'b000000011) begin // if opcode is SWAB
            result = {valD[7:0], valD[15:8]};
            N = result[7];
            Z_Flag = 0;
            C = 0;
            V = 0;
            if(result == 16'b0) begin
              Z_Flag = 1;
            end
            instruction_string = "SWAB";
          end

          else begin
          case(opcodeS)

            9'o050: begin // if opcode is CLR
              if(B == 1 && (address % 2 == 0)) begin
                result = valD;
			          result[7:0] = 8'b0;
                Z_Flag = 1;
                N = 0;
                C = 0;
                V = 0;
                instruction_string = "CLRB";
			        end
              else if(B == 1 && (address % 2 == 1)) begin
                result = valD;
			          result[15:8] = 8'b0;
                Z_Flag = 1;
                N = 0;
                C = 0;
                V = 0;
                instruction_string = "CLRB";
			        end
              else begin
                result = 16'b0;
                Z_Flag = 1;
                N = 0;
                C = 0;
                V = 0;
                instruction_string = "CLR";
              end
            end

            9'o051: begin // if opcode is COMM
              if(B == 1 && (address % 2 == 0)) begin
                result = valD;
                result[7:0] = ~valD[7:0];
                Z_Flag = 0;
                V = 0;
                C = 1;
                if(result[7:0] == 8'b0) begin
                  Z_Flag = 1;
                end
                N = result[7];
                instruction_string = "COMMB";
              end
              else if(B == 1 && (address % 2 == 1)) begin
                result = valD;
                result[15:8] = ~valD[15:8];
                Z_Flag = 0;
                V = 0;
                C = 1;
                if(result[15:8] == 8'b0) begin
                  Z_Flag = 1;
                end
                N = result[15];
                instruction_string = "COMMB";
              end
              else begin
                result = ~valD;
                Z_Flag = 0;
                V = 0;
                C = 1;
                if(result == 16'b0) begin
                  Z_Flag = 1;
                end
                N = result[15];
                instruction_string = "COMM";
                end
              end

            9'o052: begin // if opcode is INC
              if(B == 1 && (address % 2 == 0)) begin
                result = valD;
                result[7:0] = valD[7:0] + 1;
                Z_Flag = 0;
                V = 0;
                N = 0;
                if(result[7:0] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(valD == 16'o077777) begin
                  V = 1;
                end
                if(result[7:0] < 0) begin
                  N = 1;
                end
                instruction_string = "INCB";
              end
              else if(B == 1 && (address % 2 == 1)) begin
                result = valD;
                result[15:8] = valD[15:8] + 1;
                Z_Flag = 0;
                V = 0;
                N = 0;
                if(result[15:8] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(valD == 16'o077777) begin
                  V = 1;
                end
                if(result[15:8] < 0) begin
                  N = 1;
                end
                instruction_string = "INCB";
              end
              else begin
                result = valD + 1;
                Z_Flag = 0;
                N = 0;
                V = 0;
                if(valD == 16'o077777) begin
                  V = 1;
                end
                if(result == 16'b0) begin
                  Z_Flag = 1;
                end
                if(result < 0) begin
                  N = 1;
                end
                instruction_string = "INC";
              end

            end

            9'o053: begin // if opcode is DEC
              if(B == 1 && (address % 2 == 0)) begin
                result = valD;
                result[7:0] = valD[7:0] - 1;
                Z_Flag = 0;
                V = 0;
                N = 0;
                if(result[7:0] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(valD == 16'o100000) begin
                  V = 1;
                end
                if(result[7:0] < 0) begin
                  N = 1;
                end
                instruction_string = "DECB";
              end
              else if(B == 1 && (address % 2 == 1)) begin
                result = valD;
                result[15:8] = valD[15:8] - 1;
                Z_Flag = 0;
                V = 0;
                N = 0;
                if(result[15:8] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(valD == 16'o100000) begin
                  V = 1;
                end
                if(result[15:8] < 0) begin
                  N = 1;
                end
                instruction_string = "DECB";
              end
              else begin
                result = valD - 1;
                Z_Flag = 0;
                N = 0;
                V = 0;
                if(valD == 16'o100000) begin
                  V = 1;
                end
                if(result == 16'b0) begin
                  Z_Flag = 1;
                end
                if(result < 0) begin
                  N = 1;
                end
                instruction_string = "DEC";
              end

            end

            9'o054: begin // if opcode is NEG
              if(B == 1 && (address % 2 == 0)) begin
                result = valD;
                result[7:0] = -valD[7:0];
                Z_Flag = 0;
                V = 0;
                N = 0;
                C = 1;
                if(result[7:0] == 8'b0) begin
                  Z_Flag = 1;
                  C = 0;
                end
                if(result == 16'o100000) begin
                  V = 1;
                end
                if(result[7:0] < 0) begin
                  N = 1;
                end
                instruction_string = "NEGB";
              end
              else if(B == 1 && (address % 2 == 1)) begin
                result = valD;
                result[15:8] = -valD[15:8];
                Z_Flag = 0;
                V = 0;
                N = 0;
                C = 1;
                if(result[15:8] == 8'b0) begin
                  Z_Flag = 1;
                  C = 0;
                end
                if(result == 16'o100000) begin
                  V = 1;
                end
                if(result[15:8] < 0) begin
                  N = 1;
                end
                instruction_string = "NEGB";
              end
              else begin
                result = -valD;
                Z_Flag = 0;
                N = 0;
                V = 0;
                C = 1;
                if(result == 16'b0) begin
                  Z_Flag = 1;
                  C = 0;
                end
                if(result < 0) begin
                  N = 1;
                end
                if(result == 16'o100000) begin
                  V = 1;
                end
                instruction_string = "NEG";
              end
            end

            9'o055: begin // if opcode is ADC
                if(B == 1 && (address % 2 == 0)) begin
                  result = valD;
                  result[7:0] = valD[7:0] + C;
                  Z_Flag = 0;
                  N = 0;
                  V = 0;
                  C = 0;
                  if(result[7:0] == 8'b0) begin
                    Z_Flag = 1;
                  end
                  if(valD == 16'o077777 && C == 1) begin
                    V = 1;
                  end
                  if(valD == 16'o177777 && C == 1) begin
                    C = 1;
                  end
                  if(result[7:0] < 0) begin
                    N = 1;
                  end
                  instruction_string = "ADCB";
                end

                else if(B == 1 && (address % 2 == 1)) begin
                  result = valD;
                  result[15:8] = valD[15:8] + C;
                  Z_Flag = 0;
                  N = 0;
                  V = 0;
                  C = 0;
                  if(result[15:8] == 8'b0) begin
                    Z_Flag = 1;
                  end
                  if(valD == 16'o077777 && C == 1) begin
                    V = 1;
                  end
                  if(valD == 16'o177777 && C == 1) begin
                    C = 1;
                  end
                  if(result[15:8] < 0) begin
                    N = 1;
                  end
                  instruction_string = "ADCB";
                end

                else begin
                  result = valD + C;
                  Z_Flag = 0;
                  N = 0;
                  V = 0;
                  C = 0;
                  if(result == 16'b0) begin
                    Z_Flag = 1;
                  end
                  if(valD == 16'o077777 && C == 1) begin
                    V = 1;
                  end
                  if(valD == 16'o177777 && C == 1) begin
                    C = 1;
                  end
                  if(result < 0) begin
                    N = 1;
                  end
                  instruction_string = "ADC";
                end

            end

            9'o056: begin // if opcode is SBC
              if(B == 1 && (address % 2 == 0)) begin
                result = valD;
                result[7:0] = valD[7:0] - C;
                Z_Flag = 0;
                N = 0;
                V = 0;
                if(result[7:0] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(valD == 16'o100000 && C == 1) begin
                  V = 1;
                end
                if(valD == 16'o100000 && C == 1) begin
                  C = 1;
                end
                C = 0;
                if(result[7:0] < 0) begin
                  N = 1;
                end
                instruction_string = "SBCB";
              end

              else if(B == 1 && (address % 2 == 1)) begin
                result = valD;
                result[15:8] = valD[15:8] - C;
                Z_Flag = 0;
                N = 0;
                V = 0;
                if(result[15:8] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(valD == 16'o100000 && C == 1) begin
                  V = 1;
                end
                if(valD == 16'o100000 && C == 1) begin
                  C = 1;
                end
                C = 0;
                if(result[15:8] < 0) begin
                  N = 1;
                end
                instruction_string = "SBCB";
              end
              else begin
                result = valD - C;
                Z_Flag = 0;
                N = 0;
                V = 0;
                if(result == 16'b0) begin
                  Z_Flag = 1;
                end
                if(valD == 16'o100000) begin
                  V = 1;
                end
                if(valD == 16'b0 && C == 1) begin
                  C = 1;
                end
                C = 0;
                if(result < 0) begin
                  N = 1;
                end
                instruction_string = "SBC";
              end

            end

            9'o060: begin // if opcode is ROR
              if(B == 1 && (address % 2 == 0)) begin
                result = valD;
                result[7:0] = valD[7:0] >> 1;
                result[7] = C;
                Z_Flag = 0;
                N = 0;
                C = valD[0];
                V = N ^ C;
                if(result[7:0] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(result[7:0] < 0) begin
                  N = 1;
                end
                instruction_string = "ROR";
              end

              else if(B == 1 && (address % 2 == 1)) begin
                result = valD;
                result[15:8] = valD[15:8] >> 1;
                result[15] = C;
                Z_Flag = 0;
                N = 0;
                C = valD[8];
                V = N ^ C;
                if(result[15:8] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(result[15:8] < 0) begin
                  N = 1;
                end
                instruction_string = "RORB";
              end
              else begin
                result = valD >> 1;
                result[15] = C;
                Z_Flag = 0;
                N = 0;
                if(result == 16'b0) begin
                  Z_Flag = 1;
                end
                if(result < 0) begin
                  N = 1;
                end
                instruction_string = "ROR";
                C = valD[0];
                V = N ^ C;
              end
            end

            9'o061: begin // if opcode is ROL
              if(B == 1 && (address % 2 == 0)) begin
                result = valD;
                result[7:0] = valD[7:0] << 1;
                result[0] = C;
                Z_Flag = 0;
                N = 0;
                C = valD[7];
                V = N ^ C;
                if(result[7:0] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(result[7:0] < 0) begin
                  N = 1;
                end
                instruction_string = "ROLB";
              end

              else if(B == 1 && (address % 2 == 1)) begin
                result = valD;
                result[15:8] = valD[15:8] << 1;
                result[8] = C;
                Z_Flag = 0;
                N = 0;
                C = valD[15];
                V = N ^ C;
                if(result[15:8] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(result[15:8] < 0) begin
                  N = 1;
                end
                instruction_string = "ROLB";
              end
              else begin
                result = valD << 1;
                Z_Flag = 0;
                N = 0;
                result[0] = C;
                if(result == 16'b0) begin
                  Z_Flag = 1;
                end
                if(result < 0) begin
                  N = 1;
                end
                instruction_string = "ROL";
                C = valD[15];
                V = N ^ C;
              end
            end

            9'o062: begin // if opcode is ASR
              if(B == 1 && (address % 2 == 0)) begin
                result = valD;
                result[7:0] = valD[7:0] >> 1;
                result[7] = valD[7];
                Z_Flag = 0;
                N = 0;
                C = valD[0];
                V = N ^ C;
                if(result[7:0] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(result[7:0] < 0) begin
                  N = 1;
                end
                instruction_string = "ASRB";
              end

              else if(B == 1 && (address % 2 == 1)) begin
                result = valD;
                result[15:8] = valD[15:8] >> 1;
                result[15] = valD[15];
                Z_Flag = 0;
                N = 0;
                C = valD[8];
                V = N ^ C;
                if(result[15:8] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(result[15:8] < 0) begin
                  N = 1;
                end
                instruction_string = "ASRB";
              end
              else begin
                result = valD >> 1;
                result[15] = valD[15];
                Z_Flag = 0;
                N = 0;
                if(result == 16'b0) begin
                  Z_Flag = 1;
                end
                if(result < 0) begin
                  N = 1;
                end
                instruction_string = "ASR";
                C = valD[0];
                V = N ^ C;
              end
            end

            9'o063: begin // if opcode is ASL
              if(B == 1 && (address % 2 == 0)) begin
                result = valD;
                result[7:0] = valD[7:0] << 1;
                result[0] = 0;
                Z_Flag = 0;
                N = 0;
                C = valD[7];
                V = N ^ C;
                if(result[7:0] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(result[7:0] < 0) begin
                  N = 1;
                end
                instruction_string = "ASLB";
              end

              else if(B == 1 && (address % 2 == 1)) begin
                result = valD;
                result[15:8] = valD[15:8] << 1;
                result[8] = 0;
                Z_Flag = 0;
                N = 0;
                C = valD[15];
                V = N ^ C;
                if(result[15:8] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(result[15:8] < 0) begin
                  N = 1;
                end
                instruction_string = "ASLB";
              end
              else begin
                result = valD << 1;
                Z_Flag = 0;
                N = 0;
                if(result == 16'b0) begin
                  Z_Flag = 1;
                end
                if(result < 0) begin
                  N = 1;
                end
                C = valD[15];
                V = N ^ C;
                instruction_string = "ASL";
              end
            end

            9'o067: begin // if opcode is TST
              if(B == 1 && (address % 2 == 0)) begin
                Z_Flag = 0;
                N = 0;
                V = 0;
                C = 0;
                if(result[7:0] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(result[7:0] < 0) begin
                  N = 1;
                end
                instruction_string = "TSTB";
              end
              else if(B == 1 && (address % 2 == 1)) begin
                Z_Flag = 0;
                N = 0;
                V = 0;
                C = 0;
                if(result[15:8] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(result[15:8] < 0) begin
                  N = 1;
                end
                instruction_string = "TSTB";
              end
              else begin
                Z_Flag = 0;
                N = 0;
                V = 0;
                C = 0;
                if(result == 16'b0) begin
                  Z_Flag = 1;
                end
                if(result < 0) begin
                  N = 1;
                end
                instruction_string = "TST";
              end
            end
          endcase
          end

          case(modeD) // destination mode
            3'b000: begin // register addressing mode
              register[regD] = result[15:0];
            end

            3'b001: begin // register deferred addressing mode
              memory[register[regD]] = result[15:0];
              output_out = {2'b01, register[regD]};
              #100;
            end

            3'b010: begin // auto-increment addressing mode
              memory[register[regD]] = result[15:0];
              output_out = {2'b01, register[regD]};
              #100;
              register[regD] = register[regD] + 2 - B;
            end

            3'b011: begin // auto-increment deferred addressing mode
              memory[memory[register[regD]]] = result[15:0];
              //output_out = {2'b01, register[regD]};
              #100;
              output_out = {2'b01, memory[register[regD]]};
              #100;
              register[regD] = register[regD] + 2 - B;
            end

            3'b100: begin // auto-decrement addressing mode
              register[regD] = register[regD] - 2 + B;
              memory[register[regD]] = result[15:0];
              output_out = {2'b01, register[regD]};
              #100;
            end

            3'b101: begin // auto-decrement deferred addressing mode
              register[regD] = register[regD] - 2 + B;
              memory[memory[register[regD]]] = result[15:0];
              //output_out = {2'b01, register[regD]};
              #100;
              output_out = {2'b01, memory[register[regD]]};
              #100;
            end
          endcase
          end
          output_out = {2'b10, PC};
          PC = PC + 2;
        end

// ----------------------------------------------------------------------- PROGRAM CONTROL

        else if(instruction[11] == 1'b0) begin // if instruction is program control
          offset = instruction[7:0];
          opcodeB = instruction[15:8];
          single_double_flag = 2;
          modeD = instruction[5:3];
          regD = instruction[2:0];
          instruction_counter = instruction_counter + 1;
          output_out = {2'b10, PC};
          #100;
          case(modeD) // destination mode
            3'b000: begin // register addressing mode
              valD = register[regD];
              $sformat(regd_string,"R%d", regD);
            end

            3'b001: begin // register deferred addressing mode
              address = regD;
              valD = memory[regD];
              output_out = {2'b0, regD};
              #100;
              $sformat(regd_string,"(R%d)", regD);
            end

            3'b010: begin // auto-increment addressing mode
              address = regD;
              valD = memory[regD];
              output_out = {2'b0, regD};
              #100
              $sformat(regd_string,"(R%d)+", regD);
            end

            3'b011: begin // auto-increment deferred addressing mode
              address = memory[regD];
              output_out = {2'b0, regD};
              #100;
              valD = memory[memory[regD]];
              output_out = {2'b0, memory[regD]};
              #100
              $sformat(regd_string,"@(R%d)+", regD);
            end

            3'b100: begin // auto-decrement addressing mode
              address = regD;
              valD = memory[regD];
              output_out = {2'b0, regD};
              #100;
              $sformat(regd_string,"-(R%d)", regD);
            end

            3'b101: begin // auto-decrement deferred addressing mode
              valD = memory[memory[regD]];
              address = memory[regD];
              output_out = {2'b0, regD};
              #100
              output_out = {2'b0, memory[regD]};
              #100;
              $sformat(regd_string,"@-(R%d)", regD);
            end
          endcase
          case(opcodeB)
            8'b00000000: begin // JMP
              if(instruction[6] == 1) begin
                PC = valD + 2;
                instruction_string = "JMP";
                PC_temp = PC;
                J_flag = 1'b1;
              end
              end
            8'b00000001: begin // BR
              register[6] = PC;
              offset_temp = offset << 1;
              PC = PC + offset_temp + 2;
              instruction_string = "BR";
              B_flag = 1'b1;
              end
            8'b00000010: begin // BNE
              if(Z_Flag == 1'b0)begin
                register[6] = PC;
                offset_temp = offset << 1;
                PC  = PC + offset_temp;
                B_flag = 1'b1;
              end
              PC = PC + 2;
              instruction_string = "BNE";
              end
            8'b00000011: begin // BEQ
            if(Z_Flag == 1'b1)begin
              register[6] = PC;
              offset_temp = offset << 1;
              PC  = PC + offset_temp;
              B_flag = 1'b1;
            end
            PC = PC + 2;
            instruction_string = "BEQ";
            end
            8'b10000000: begin // BPL
            if(N == 1'b0) begin
              register[6] = PC;
              offset_temp = offset << 1;
              PC  = PC + offset_temp;
              B_flag = 1'b1;
            end
            PC = PC + 2;
            instruction_string = "BPL";
            end
            8'b10000001: begin // BMI
            if(N == 1'b1) begin
              register[6] = PC;
              offset_temp = offset << 1;
              PC  = PC + offset_temp;
              B_flag = 1'b1;
            end
            PC = PC + 2;
            instruction_string = "BMI";
            end
            8'b10000100: begin // BVC
            if(V == 1'b0) begin
              register[6] = PC;
              offset_temp = offset << 1;
              PC  = PC + offset_temp;
              B_flag = 1'b1;
            end
            PC = PC + 2;
            instruction_string = "BVC";
            end
            8'b10000101: begin // BVS
            if(V == 1'b1) begin
              register[6] = PC;
              offset_temp = offset << 1;
              PC  = PC + offset_temp;
              B_flag = 1'b1;
            end
            PC = PC + 2;
            instruction_string = "BVS";
            end
            8'b10000110: begin // BHIS
            if(C == 1'b0) begin
              offset_temp = offset << 1;
              PC  = PC + offset_temp;
              B_flag = 1'b1;
            end
            PC = PC + 2;
            instruction_string = "BHIS";
            end
            8'b10000110: begin // BCC
            if(C == 1'b0) begin
              register[6] = PC;
              offset_temp = offset << 1;
              PC  = PC + offset_temp;
              B_flag = 1'b1;
            end
            PC = PC + 2;
            instruction_string = "BCC";
            end
            8'b10000111: begin // BLO
            if(C == 1'b1) begin
              register[6] = PC;
              offset_temp = offset << 1;
              PC  = PC + offset_temp;
              B_flag = 1'b1;
            end
            PC = PC + 2;
            instruction_string = "BLO";
            end
            8'b10000111: begin // BCS
            if(C == 1'b1) begin
              register[6] = PC;
              offset_temp = offset << 1;
              PC  = PC + offset_temp;
              B_flag = 1'b1;
            end
            PC = PC + 2;
            instruction_string = "BCS";
            end
            8'b00000100: begin // BGE
            if(N == 1'b0 || V == 1'b0) begin
              register[6] = PC;
              offset_temp = offset << 1;
              PC  = PC + offset_temp;
              B_flag = 1'b1;
            end
            PC = PC + 2;
            instruction_string = "BGE";
            end
            8'b00000101: begin // BLT
            if(N == 1'b1 || V == 1'b1) begin
              register[6] = PC;
              offset_temp = offset << 1;
              PC  = PC + offset_temp;
              B_flag = 1'b1;
            end
            PC = PC + 2;
            instruction_string = "BLT";
            end
            8'b00000110: begin // BGT
            if(Z_Flag == 1'b0 || (N ^ V) == 1'b0) begin
              register[6] = PC;
              offset_temp = offset << 1;
              PC  = PC + offset_temp;
              B_flag = 1'b1;
            end
            PC = PC + 2;
            instruction_string = "BGT";
            end
            8'b00000111: begin // BLE
            if(Z_Flag == 1'b1 || (N ^ V) == 1'b1) begin
              register[6] = PC;
              offset_temp = offset << 1;
              PC  = PC + offset_temp;
              B_flag = 1'b1;
            end
            PC = PC + 2;
            instruction_string = "BLE";
            end
            8'b10000010: begin // BHI
            if(Z_Flag == 1'b0 || C == 1'b0) begin
              register[6] = PC;
              offset_temp = offset << 1;
              PC  = PC + offset_temp;
              B_flag = 1'b1;
            end
            PC = PC + 2;
            instruction_string = "BHI";
            end
            8'b10000011: begin // BLOS
            if(C == 1'b1) begin
              register[6] = PC;
              offset_temp = offset << 1;
              PC  = PC + offset_temp;
              B_flag = 1'b1;
            end
            PC = PC + 2;
            instruction_string = "BLOS";
            end
          endcase

        end
      end

// ----------------------------------------------------------------------- DOUBLE OPERAND

      else if(instruction[14:12] != 3'b000) begin // if instruction is double operand
      modeS = instruction[11:9];
      regS = instruction[8:6];
      modeD = instruction[5:3];
      regD = instruction[2:0];
      opcodeD = instruction[14:12];
      single_double_flag = 0;

        if(modeS == 3'h6 || modeS == 3'h7 || modeD == 3'h6 || modeD == 3'h7 || regS == 3'h7 || regD == 3'h7) begin // if instruction is a double liner set flag
          next_instruction_flag = 1;
          single_double_flag = 0;
          output_out = {2'b10, PC};
          PC = PC + 2;
        end

        else begin
          instruction_counter = instruction_counter + 1;
          if(instruction[15:12] == 4'b1110) begin
            B_bit = 0;
          end
          else begin
            B_bit = B;
          end
          case(modeD) // destination mode
            3'b000: begin // register addressing mode
              valD = register[regD];
              $sformat(regd_string,"R%d", regD);
            end

            3'b001: begin // register deferred addressing mode
              address = register[regD];
              valD = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100;
              $sformat(regd_string,"(R%d)", regD);
            end

            3'b010: begin // auto-increment addressing mode
              address = register[regD];
              valD = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100
              $sformat(regd_string,"(R%d)+", regD);
            end

            3'b011: begin // auto-increment deferred addressing mode
              address = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100
              valD = memory[memory[register[regD]]];
              output_out = {2'b0, memory[register[regD]]};
              #100
              $sformat(regd_string,"@(R%d)+", regD);
            end

            3'b100: begin // auto-decrement addressing mode
              address = register[regD];
              valD = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100;
              $sformat(regd_string,"-(R%d)", regD);
            end

            3'b101: begin // auto-decrement deferred addressing mode
              valD = memory[memory[register[regD]]];
              address = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100
              output_out = {2'b0, memory[register[regD]]};
              #100;
              $sformat(regd_string,"@-(R%d)", regD);
            end
          endcase

          if(opcodeD != 3'h7) begin
          case(modeS) // source mode
            3'b000: begin // register addressing mode
              valS = register[regS];
              $sformat(regs_string,"R%d", regS);
            end

            3'b001: begin // register deferred addressing mode
              valS = memory[register[regS]];
              output_out = {2'b0, register[regS]};
              #100;
              $sformat(regs_string,"(R%d)", regS);
            end

            3'b010: begin // auto-increment addressing mode
              valS = memory[register[regS]];
              output_out = {2'b0, register[regS]};
              #100;
              $sformat(regs_string,"(R%d)+", regS);
              register[regS] = register[regS] + 2 - B_bit;
            end

            3'b011: begin // auto-increment deferred addressing mode
              valS = memory[memory[register[regS]]];
              output_out = {2'b0, register[regS]};
              #100;
              output_out = {2'b0, memory[register[regS]]};
              #100;
              $sformat(regs_string,"@(R%d)+", regS);
              register[regS] = register[regS] + 2 - B_bit;
            end

            3'b100: begin // auto-decrement addressing mode
              register[regS] = register[regS] - 2 + B_bit;
              valS = memory[register[regS]];
              output_out = {2'b0, register[regS]};
              #100;
              $sformat(regs_string,"-(R%d)", regS);
            end

            3'b101: begin // auto-decrement deferred addressing mode
              register[regS] = register[regS] - 2 + B_bit;
              valS = memory[memory[register[regS]]];
              output_out = {2'b0, register[regS]};
              #100;
              $sformat(regs_string,"@-(R%d)", regS);
              output_out = {2'b0, memory[register[regS]]};
              #100;
            end
          endcase
          end

          case(opcodeD)
            3'b001: begin // if opcode is MOV
              if(B == 1) begin
                result = valS;
                result[15:8] = {8{valS[7]}};
                N = 0;
                Z_Flag = 0;
                if(result == 16'b0) begin
                  Z_Flag = 1;
                end
                V = 0;
                if(result < 0) begin
                  N = 1;
                  Z_Flag = 0;
                end
                instruction_string = "MOVB";
              end
              else begin
                result = valS;
                N = 0;
                Z_Flag = 0;
                if(result == 16'b0) begin
                  Z_Flag = 1;
                end
                V = 0;
                if(result < 0) begin
                  N = 1;
                  Z_Flag = 0;
                end
                instruction_string = "MOV";
              end
            end

            3'b010: begin // if opcode is CMP
              if(B == 1 && (address % 2 == 0)) begin
                result_temp[7:0] = valS[7:0] - valD[7:0];
                Z_Flag = 0;
                N = 0;
                V = 0;
                C = 1;
                if(result_temp[7:0] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(result_temp[7:0] < 0) begin
                  N = 1;
                end
                instruction_string = "CMPB";
              end
              else if(B == 1 && (address % 2 == 1)) begin
                result_temp[15:8] = valS[15:8] - valD[15:8];
                Z_Flag = 0;
                N = 0;
                V = 0;
                C = 1;
                if(result_temp[15:8] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(result_temp[15:8] < 0) begin
                  N = 1;
                end
                instruction_string = "CMPB";
              end
              else begin
                result_temp = valS - valD;
                Z_Flag = 0;
                N = 0;
                V = 0;
                C = 1;
                if(result_temp == 16'b0) begin
                  Z_Flag = 1;
                end
                if(result_temp < 0) begin
                  N = 1;
                end
                instruction_string = "CMP";
              end
            end

            3'b110: begin // if opcode is ADD/SUB
              if(B == 0) begin // if opcode is ADD
                  result = valD + valS;
                  C = valD[15] & valS[15];
                  N = 0;
                  Z_Flag = 0;
                  V = 0;
                  if(result == 17'b0) begin
                    Z_Flag = 1;
                  end
                  if(result < 0) begin
                    N = 1;
                  end
                  instruction_string = "ADD";
              end
              else if(B == 1) begin // if opcode is SUB
                result = valD - valS;
                C = 1;
                N = 0;
                Z_Flag = 0;
                V = 0;
                if(result == 17'b0) begin
                  Z_Flag = 1;
                end
                if(result < 0) begin
                  N = 1;
                end
                instruction_string = "SUB";
              end
            end

            3'b011: begin // if opcode is BIT
              if(B == 1 && (address % 2 == 0)) begin
                result_temp[7:0] = valS[7:0] & valD[7:0];
                Z_Flag = 0;
                V = 0;
                N = result_temp[7];
                if(result_temp[7:0] == 8'b0) begin
                  Z_Flag = 1;
                end
                instruction_string = "BITB";
              end
              else if(B == 1 && (address % 2 == 1)) begin
                result_temp[15:8] = valS[15:8] & valD[15:8];
                Z_Flag = 0;
                V = 0;
                N = result_temp[15];
                if(result_temp[15:8] == 8'b0) begin
                  Z_Flag = 1;
                end
                instruction_string = "BITB";
              end
              else begin
                result_temp = valS & valD;
                Z_Flag = 0;
                V = 0;
                N = result_temp[15];
                if(result_temp == 17'b0) begin
                  Z_Flag = 1;
                end
                instruction_string = "BIT";
              end


            end

            3'b100: begin // if opcode is BIC
              if(B == 1 && (address % 2 == 0)) begin
                result[7:0] = ~(valS[7:0]) & valD[7:0];
                Z_Flag = 0;
                V = 0;
                N = result[7];
                if(result[7:0] == 8'b0) begin
                  Z_Flag = 1;
                end
                instruction_string = "BICB";
              end
              else if(B == 1 && (address % 2 == 1)) begin
                result[15:8] = ~(valS[15:8]) & valD[15:8];
                Z_Flag = 0;
                V = 0;
                N = result[15];
                if(result[15:8] == 8'b0) begin
                  Z_Flag = 1;
                end
                instruction_string = "BICB";
              end
              else begin
                result = ~(valS) & valD;
                N = result[15];
                Z_Flag = 0;
                V = 0;
                if(result == 16'b0) begin
                  Z_Flag = 1;
                end
                instruction_string = "BIC";
              end

            end

            3'b101: begin // if opcode is BIS
              if(B == 1 && (address % 2 == 0)) begin
                result[7:0] = valS[7:0] | valD[7:0];
                Z_Flag = 0;
                V = 0;
                N = result[7];
                if(result[7:0] == 8'b0) begin
                  Z_Flag = 1;
                end
                instruction_string = "BISB";
              end
              else if(B == 1 && (address % 2 == 1)) begin
                result[15:8] = valS[15:8] | valD[15:8];
                Z_Flag = 0;
                V = 0;
                N = result[15];
                if(result[15:8] == 8'b0) begin
                  Z_Flag = 1;
                end
                instruction_string = "BISB";
              end
              else begin
                result = valS | valD;
                N = result[15];
                Z_Flag = 0;
                V = 0;
                if(result == 16'b0) begin
                  Z_Flag = 1;
                end
                instruction_string = "BIS";
              end
            end

            3'b111: begin // if opcode is MUL/DIV/ASH/ASHC/XOR

              if(regD == 3'h7) begin
                case(modeD)
                  3'b010: begin
                    $sformat(regs_string,"#%o", instruction);
                  end
                  3'b011: begin
                    $sformat(regs_string,"@#%o", instruction);
                  end
                  3'b110: begin
                    $sformat(regs_string,"%o", instruction);
                  end
                  3'b111: begin
                    $sformat(regs_string,"@%o", instruction);
                  end
                endcase
              end
              else if(regD != 3'h7) begin
                case(modeD) // source mode
                  3'b000: begin // register addressing mode
                    $sformat(regs_string,"R%d", regD);
                  end

                  3'b001: begin // register deferred addressing mode
                    $sformat(regs_string,"(R%d)", regD);
                  end

                  3'b010: begin // auto-increment addressing mode
                    $sformat(regs_string,"(R%d)+", regD);
                  end

                  3'b011: begin // auto-increment deferred addressing mode
                    $sformat(regs_string,"@(R%d)+", regD);
                  end

                  3'b100: begin // auto-decrement addressing mode
                    $sformat(regs_string,"-(R%d)", regD);
                  end

                  3'b101: begin // auto-decrement deferred addressing mode
                    $sformat(regs_string,"@-(R%d)", regD);
                  end

                  3'b110: begin
                    $sformat(regs_string,"%o(R%d)", instruction,regD);
                  end

                  3'b111: begin
                    $sformat(regs_string,"@%o(R%d)", instruction,regD);
                  end
                endcase
              end

              case(modeS)
                3'b000: begin // if opcode is MUL
                  instruction_string = "MUL";
                  $sformat(regd_string,"R%d", regS);
                  mul_result = register[regS] * valD;
                  V = 0;
                  N = 0;
                  Z_Flag = 0;
                  if(regS % 2 == 0) begin
                    register[regS] = mul_result[31:16];
                    result = mul_result[31:16];
                    register[regS + 1] = mul_result[15:0];
                  end
                  else begin
                    result = mul_result[31:16];
                    register[regS] = mul_result[15:0];
                  end
                  if(mul_result < -32768 || mul_result > 32767) begin
                    C = 1;
                  end
                  if(mul_result == 32'b0) begin
                    Z_Flag = 1;
                  end
                  if(mul_result < 0) begin
                    N = 1;
                  end
                end

                3'b001: begin // if opcode is DIV
                  remainder = register[regS] % valD;
                  register[regS] = register[regS] - remainder;
                  register[regS] = register[regS]/valD;
                  register[regS+1] = remainder;
                  N = 0;
                  Z_Flag = 0;
                  C = 0;
                  if(register[regS] < 0) begin
                    N = 1;
                  end
                  else if(register[regS] == 0) begin
                    Z_Flag = 1;
                  end
                  else if(valD == 0) begin
                    V = 1;
                    C = 1;
                  end
                  instruction_string = "DIV";
                  $sformat(regd_string,"R%d", regS);
                end

                3'b010: begin // if opcode is ASH
                  shift = valD[5:0];
                  result_temp = register[regS];
                  Z_Flag = 0;
                  N = 0;
                  V = 0;
                  if(shift < 0) begin
                    C = result_temp[0];
                  end
                  else begin
                    C = result_temp[15];
                  end
                  register[regS] = result_temp << shift;
                  if(register[regS] == 16'b0) begin
                    Z_Flag = 1;
                  end
                  if(register[regS] < 0) begin
                    N = 1;
                  end
                  if(result_temp[15] != register[regS][15]) begin
                    V = 1;
                  end
                  instruction_string = "ASH";
                  $sformat(regd_string,"R%d", regS);
                end

                3'b011: begin // if opcode is ASHC
                  instruction_string = "ASHC";
                  $sformat(regd_string,"R%d", regS);
                  if(regS % 2 == 0) begin
                    mul_result = {register[regS], register[regS+1]};
                    mul_result = mul_result >> instruction[5:0];
                    Z_Flag = 0;
                    N = 0;
                    V = 0;
                    if(instruction[5] == 1) begin
                      C = register[regS][15];
                    end
                    if(instruction[5] == 0) begin
                      C = register[regS+1][0];
                    end
                    if(mul_result < 0) begin
                      N = 1;
                    end
                    if(mul_result == 32'b0) begin
                      Z_Flag = 1;
                    end
                    if(mul_result[31] != register[regS][15]) begin
                      V = 1;
                    end
                    register[regS] = mul_result[31:16];
                    register[regS + 1] = mul_result[15:0];
                  end
                  else begin
                    mul_result = {register[regS-1], register[regS]};
                    mul_result = mul_result >> instruction[5:0];
                    Z_Flag = 0;
                    N = 0;
                    V = 0;
                    if(instruction[5] == 1) begin
                      C = register[regS-1][15];
                    end
                    if(instruction[5] == 0) begin
                      C = register[regS][0];
                    end
                    if(mul_result < 0) begin
                      N = 1;
                    end
                    if(mul_result == 32'b0) begin
                      Z_Flag = 1;
                    end
                    if(mul_result[31] != register[regS-1][15]) begin
                      V = 1;
                    end
                    register[regS-1] = mul_result[31:16];
                    register[regS] = mul_result[15:0];
                  end
                end

                3'b100: begin // if opcode is XOR
                  result = valD ^ register[regS];
                  N = 0;
                  Z_Flag = 0;
                  V = 0;
                  if(result == 17'b0) begin
                    Z_Flag = 1;
                  end
                  if(result < 0) begin
                    N = 1;
                  end
                  instruction_string = "XOR";
                  $sformat(regs_string,"R%d", regS);
                end
              endcase
            end
          endcase

          if({opcodeD, modeS} != 6'o70 || {opcodeD, modeS} != 6'o71 || {opcodeD, modeS} != 6'o72 || {opcodeD, modeS} != 6'o73) begin
          case(modeD) // destination mode
            3'b000: begin // register addressing mode
              register[regD] = result[15:0];
            end

            3'b001: begin // register deferred addressing mode
              memory[register[regD]] = result[15:0];
              output_out = {2'b01, register[regD]};
              #100;
            end

            3'b010: begin // auto-increment addressing mode
              memory[register[regD]] = result[15:0];
              output_out = {2'b01, register[regD]};
              #100;
              register[regD] = register[regD] + 2 - B_bit;
            end

            3'b011: begin // auto-increment deferred addressing mode
              memory[memory[register[regD]]] = result[15:0];
              //output_out = {2'b01, register[regD]};
              #100;
              output_out = {2'b01, memory[register[regD]]};
              #100;
              register[regD] = register[regD] + 2 - B_bit;
            end

            3'b100: begin // auto-decrement addressing mode
              register[regD] = register[regD] - 2 + B_bit;
              memory[register[regD]] = result[15:0];
              output_out = {2'b01, register[regD]};
              #100;
            end

            3'b101: begin // auto-decrement deferred addressing mode
              register[regD] = register[regD] - 2 + B_bit;
              memory[memory[register[regD]]] = result[15:0];
              //output_out = {2'b01, register[regD]};
              #100;
              output_out = {2'b01, memory[register[regD]]};
              #100;
            end
          endcase
          end

          output_out = {2'b10, PC};
          PC = PC + 2;
        end
      end

    end

// ----------------------------------------------------------------------- DOUBLE LINER INSTRUCTIONS

    else if(next_instruction_flag == 1) begin // if instruction was preceded by a double liner
      memory[PC] = instruction;
      PC_read = PC + 2;


// ----------------------------------------------------------------------- SINGLE OPERAND

      if(single_double_flag == 1) begin
        instruction_counter = instruction_counter + 1;
        if(regD == 3'h7) begin
          case(modeD)
            3'b010: begin
              valD = instruction;
            end
            3'b011: begin
              output_out = {2'b0, PC};
              #100
              output_out = {2'h0, instruction};
              #100
              valD = memory[instruction];
            end
            3'b110: begin
              output_out = {2'b0, PC};
              #100
              output_out = {2'h0, PC_read + instruction};
              #100
              valD = memory[PC_read + instruction];
            end
            3'b111: begin
              output_out = {2'b0, PC};
              #100
              output_out = {2'h0, PC_read + instruction};
              #100
              output_out = {2'h0, memory[PC_read + instruction]};
              #100
              valD = memory[memory[PC_read + instruction]];
            end
          endcase
        end
        else begin
          case(modeD) // source mode
            3'b000: begin // register addressing mode
              valD = register[regD];
            end

            3'b001: begin // register deferred addressing mode
              address = register[regD];
              valD = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100;
            end

            3'b010: begin // auto-increment addressing mode
              address = register[regD];
              valD = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100;
            end

            3'b011: begin // auto-increment deferred addressing mode
              address = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100;
              valD = memory[memory[register[regD]]];
              output_out = {2'b0, memory[register[regD]]};
              #100;
            end

            3'b100: begin // auto-decrement addressing mode
              address = register[regD];
              valD = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100;
            end

            3'b101: begin // auto-decrement deferred addressing mode
              valD = memory[memory[register[regD]]];
              address = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100;
              output_out = {2'b0, memory[register[regD]]};
              #100;
            end

            3'b110: begin
              output_out = {2'b0, register[regD] + instruction};
              #100
              valD = memory[register[regD] + instruction];
            end

            3'b111: begin
              output_out = {2'b0, register[regD] + instruction};
              #100
              output_out = {2'b0, memory[register[regD] + instruction]};
              #100
              valD = memory[memory[register[regD] + instruction]];
            end
          endcase
        end

        // COPY OF SINGLE OPERAND INSTRUCTIONS HERE

        if(old_instruction[14:6] == 9'b000000011) begin // if opcode is SWAB
          result = {valD[7:0], valD[15:8]};
          N = result[7];
          Z_Flag = 0;
          C = 0;
          V = 0;
          if(result == 16'b0) begin
            Z_Flag = 1;
          end
          instruction_string = "SWAB";
        end

        case(opcodeS)

          9'o050: begin // if opcode is CLR
            if(B == 1 && (address % 2 == 0)) begin
              result = valD;
              result[7:0] = 8'b0;
              Z_Flag = 1;
              N = 0;
              C = 0;
              V = 0;
              instruction_string = "CLRB";
            end
            else if(B == 1 && (address % 2 == 1)) begin
              result = valD;
              result[15:8] = 8'b0;
              Z_Flag = 1;
              N = 0;
              C = 0;
              V = 0;
              instruction_string = "CLRB";
            end
            else begin
              result = 16'b0;
              Z_Flag = 1;
              N = 0;
              C = 0;
              V = 0;
              instruction_string = "CLR";
            end
          end

          9'o051: begin // if opcode is COMM
            if(B == 1 && (address % 2 == 0)) begin
              result = valD;
              result[7:0] = ~valD[7:0];
              Z_Flag = 0;
              V = 0;
              C = 1;
              if(result[7:0] == 8'b0) begin
                Z_Flag = 1;
              end
              N = result[7];
              instruction_string = "COMMB";
            end
            else if(B == 1 && (address % 2 == 1)) begin
              result = valD;
              result[15:8] = ~valD[15:8];
              Z_Flag = 0;
              V = 0;
              C = 1;
              if(result[15:8] == 8'b0) begin
                Z_Flag = 1;
              end
              N = result[15];
              instruction_string = "COMMB";
            end
            else begin
              result = ~valD;
              Z_Flag = 0;
              V = 0;
              C = 1;
              if(result == 16'b0) begin
                Z_Flag = 1;
              end
              N = result[15];
              instruction_string = "COMM";
              end
            end

          9'o052: begin // if opcode is INC
            if(B == 1 && (address % 2 == 0)) begin
              result = valD;
              result[7:0] = valD[7:0] + 1;
              Z_Flag = 0;
              V = 0;
              N = 0;
              if(result[7:0] == 8'b0) begin
                Z_Flag = 1;
              end
              if(valD == 16'o077777) begin
                V = 1;
              end
              if(result[7:0] < 0) begin
                N = 1;
              end
              instruction_string = "INCB";
            end
            else if(B == 1 && (address % 2 == 1)) begin
              result = valD;
              result[15:8] = valD[15:8] + 1;
              Z_Flag = 0;
              V = 0;
              N = 0;
              if(result[15:8] == 8'b0) begin
                Z_Flag = 1;
              end
              if(valD == 16'o077777) begin
                V = 1;
              end
              if(result[15:8] < 0) begin
                N = 1;
              end
              instruction_string = "INCB";
            end
            else begin
              result = valD + 1;
              Z_Flag = 0;
              N = 0;
              V = 0;
              if(valD == 16'o077777) begin
                V = 1;
              end
              if(result == 16'b0) begin
                Z_Flag = 1;
              end
              if(result < 0) begin
                N = 1;
              end
              instruction_string = "INC";
            end

          end

          9'o053: begin // if opcode is DEC
            if(B == 1 && (address % 2 == 0)) begin
              result = valD;
              result[7:0] = valD[7:0] - 1;
              Z_Flag = 0;
              V = 0;
              N = 0;
              if(result[7:0] == 8'b0) begin
                Z_Flag = 1;
              end
              if(valD == 16'o100000) begin
                V = 1;
              end
              if(result[7:0] < 0) begin
                N = 1;
              end
              instruction_string = "DECB";
            end
            else if(B == 1 && (address % 2 == 1)) begin
              result = valD;
              result[15:8] = valD[15:8] - 1;
              Z_Flag = 0;
              V = 0;
              N = 0;
              if(result[15:8] == 8'b0) begin
                Z_Flag = 1;
              end
              if(valD == 16'o100000) begin
                V = 1;
              end
              if(result[15:8] < 0) begin
                N = 1;
              end
              instruction_string = "DECB";
            end
            else begin
              result = valD - 1;
              Z_Flag = 0;
              N = 0;
              V = 0;
              if(valD == 16'o100000) begin
                V = 1;
              end
              if(result == 16'b0) begin
                Z_Flag = 1;
              end
              if(result < 0) begin
                N = 1;
              end
              instruction_string = "DEC";
            end

          end

          9'o054: begin // if opcode is NEG
            if(B == 1 && (address % 2 == 0)) begin
              result = valD;
              result[7:0] = -valD[7:0];
              Z_Flag = 0;
              V = 0;
              N = 0;
              C = 1;
              if(result[7:0] == 8'b0) begin
                Z_Flag = 1;
                C = 0;
              end
              if(result == 16'o100000) begin
                V = 1;
              end
              if(result[7:0] < 0) begin
                N = 1;
              end
              instruction_string = "NEGB";
            end
            else if(B == 1 && (address % 2 == 1)) begin
              result = valD;
              result[15:8] = -valD[15:8];
              Z_Flag = 0;
              V = 0;
              N = 0;
              C = 1;
              if(result[15:8] == 8'b0) begin
                Z_Flag = 1;
                C = 0;
              end
              if(result == 16'o100000) begin
                V = 1;
              end
              if(result[15:8] < 0) begin
                N = 1;
              end
              instruction_string = "NEGB";
            end
            else begin
              result = -valD;
              Z_Flag = 0;
              N = 0;
              V = 0;
              C = 1;
              if(result == 16'b0) begin
                Z_Flag = 1;
                C = 0;
              end
              if(result < 0) begin
                N = 1;
              end
              if(result == 16'o100000) begin
                V = 1;
              end
              instruction_string = "NEG";
            end
          end

          9'o055: begin // if opcode is ADC
              if(B == 1 && (address % 2 == 0)) begin
                result = valD;
                result[7:0] = valD[7:0] + C;
                Z_Flag = 0;
                N = 0;
                V = 0;
                C = 0;
                if(result[7:0] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(valD == 16'o077777 && C == 1) begin
                  V = 1;
                end
                if(valD == 16'o177777 && C == 1) begin
                  C = 1;
                end
                if(result[7:0] < 0) begin
                  N = 1;
                end
                instruction_string = "ADCB";
              end

              else if(B == 1 && (address % 2 == 1)) begin
                result = valD;
                result[15:8] = valD[15:8] + C;
                Z_Flag = 0;
                N = 0;
                V = 0;
                C = 0;
                if(result[15:8] == 8'b0) begin
                  Z_Flag = 1;
                end
                if(valD == 16'o077777 && C == 1) begin
                  V = 1;
                end
                if(valD == 16'o177777 && C == 1) begin
                  C = 1;
                end
                if(result[15:8] < 0) begin
                  N = 1;
                end
                instruction_string = "ADCB";
              end

              else begin
                result = valD + C;
                Z_Flag = 0;
                N = 0;
                V = 0;
                C = 0;
                if(result == 16'b0) begin
                  Z_Flag = 1;
                end
                if(valD == 16'o077777 && C == 1) begin
                  V = 1;
                end
                if(valD == 16'o177777 && C == 1) begin
                  C = 1;
                end
                if(result < 0) begin
                  N = 1;
                end
                instruction_string = "ADC";
              end

          end

          9'o056: begin // if opcode is SBC
            if(B == 1 && (address % 2 == 0)) begin
              result = valD;
              result[7:0] = valD[7:0] - C;
              Z_Flag = 0;
              N = 0;
              V = 0;
              if(result[7:0] == 8'b0) begin
                Z_Flag = 1;
              end
              if(valD == 16'o100000 && C == 1) begin
                V = 1;
              end
              if(valD == 16'o100000 && C == 1) begin
                C = 1;
              end
              C = 0;
              if(result[7:0] < 0) begin
                N = 1;
              end
              instruction_string = "SBCB";
            end

            else if(B == 1 && (address % 2 == 1)) begin
              result = valD;
              result[15:8] = valD[15:8] - C;
              Z_Flag = 0;
              N = 0;
              V = 0;
              if(result[15:8] == 8'b0) begin
                Z_Flag = 1;
              end
              if(valD == 16'o100000 && C == 1) begin
                V = 1;
              end
              if(valD == 16'o100000 && C == 1) begin
                C = 1;
              end
              C = 0;
              if(result[15:8] < 0) begin
                N = 1;
              end
              instruction_string = "SBCB";
            end
            else begin
              result = valD - C;
              Z_Flag = 0;
              N = 0;
              V = 0;
              if(result == 16'b0) begin
                Z_Flag = 1;
              end
              if(valD == 16'o100000) begin
                V = 1;
              end
              if(valD == 16'b0 && C == 1) begin
                C = 1;
              end
              C = 0;
              if(result < 0) begin
                N = 1;
              end
              instruction_string = "SBC";
            end

          end

          9'o060: begin // if opcode is ROR
            if(B == 1 && (address % 2 == 0)) begin
              result = valD;
              result[7:0] = valD[7:0] >> 1;
              result[7] = C;
              Z_Flag = 0;
              N = 0;
              C = valD[0];
              V = N ^ C;
              if(result[7:0] == 8'b0) begin
                Z_Flag = 1;
              end
              if(result[7:0] < 0) begin
                N = 1;
              end
              instruction_string = "ROR";
            end

            else if(B == 1 && (address % 2 == 1)) begin
              result = valD;
              result[15:8] = valD[15:8] >> 1;
              result[15] = C;
              Z_Flag = 0;
              N = 0;
              C = valD[8];
              V = N ^ C;
              if(result[15:8] == 8'b0) begin
                Z_Flag = 1;
              end
              if(result[15:8] < 0) begin
                N = 1;
              end
              instruction_string = "RORB";
            end
            else begin
              result = valD >> 1;
              result[15] = C;
              Z_Flag = 0;
              N = 0;
              if(result == 16'b0) begin
                Z_Flag = 1;
              end
              if(result < 0) begin
                N = 1;
              end
              instruction_string = "ROR";
              C = valD[0];
              V = N ^ C;
            end
          end

          9'o061: begin // if opcode is ROL
            if(B == 1 && (address % 2 == 0)) begin
              result = valD;
              result[7:0] = valD[7:0] << 1;
              result[0] = C;
              Z_Flag = 0;
              N = 0;
              C = valD[7];
              V = N ^ C;
              if(result[7:0] == 8'b0) begin
                Z_Flag = 1;
              end
              if(result[7:0] < 0) begin
                N = 1;
              end
              instruction_string = "ROLB";
            end

            else if(B == 1 && (address % 2 == 1)) begin
              result = valD;
              result[15:8] = valD[15:8] << 1;
              result[8] = C;
              Z_Flag = 0;
              N = 0;
              C = valD[15];
              V = N ^ C;
              if(result[15:8] == 8'b0) begin
                Z_Flag = 1;
              end
              if(result[15:8] < 0) begin
                N = 1;
              end
              instruction_string = "ROLB";
            end
            else begin
              result = valD << 1;
              Z_Flag = 0;
              N = 0;
              result[0] = C;
              if(result == 16'b0) begin
                Z_Flag = 1;
              end
              if(result < 0) begin
                N = 1;
              end
              instruction_string = "ROL";
              C = valD[15];
              V = N ^ C;
            end
          end

          9'o062: begin // if opcode is ASR
            if(B == 1 && (address % 2 == 0)) begin
              result = valD;
              result[7:0] = valD[7:0] >> 1;
              result[7] = valD[7];
              Z_Flag = 0;
              N = 0;
              C = valD[0];
              V = N ^ C;
              if(result[7:0] == 8'b0) begin
                Z_Flag = 1;
              end
              if(result[7:0] < 0) begin
                N = 1;
              end
              instruction_string = "ASRB";
            end

            else if(B == 1 && (address % 2 == 1)) begin
              result = valD;
              result[15:8] = valD[15:8] >> 1;
              result[15] = valD[15];
              Z_Flag = 0;
              N = 0;
              C = valD[8];
              V = N ^ C;
              if(result[15:8] == 8'b0) begin
                Z_Flag = 1;
              end
              if(result[15:8] < 0) begin
                N = 1;
              end
              instruction_string = "ASRB";
            end
            else begin
              result = valD >> 1;
              result[15] = valD[15];
              Z_Flag = 0;
              N = 0;
              if(result == 16'b0) begin
                Z_Flag = 1;
              end
              if(result < 0) begin
                N = 1;
              end
              instruction_string = "ASR";
              C = valD[0];
              V = N ^ C;
            end
          end

          9'o063: begin // if opcode is ASL
            if(B == 1 && (address % 2 == 0)) begin
              result = valD;
              result[7:0] = valD[7:0] << 1;
              result[0] = 0;
              Z_Flag = 0;
              N = 0;
              C = valD[7];
              V = N ^ C;
              if(result[7:0] == 8'b0) begin
                Z_Flag = 1;
              end
              if(result[7:0] < 0) begin
                N = 1;
              end
              instruction_string = "ASLB";
            end

            else if(B == 1 && (address % 2 == 1)) begin
              result = valD;
              result[15:8] = valD[15:8] << 1;
              result[8] = 0;
              Z_Flag = 0;
              N = 0;
              C = valD[15];
              V = N ^ C;
              if(result[15:8] == 8'b0) begin
                Z_Flag = 1;
              end
              if(result[15:8] < 0) begin
                N = 1;
              end
              instruction_string = "ASLB";
            end
            else begin
              result = valD << 1;
              Z_Flag = 0;
              N = 0;
              if(result == 16'b0) begin
                Z_Flag = 1;
              end
              if(result < 0) begin
                N = 1;
              end
              C = valD[15];
              V = N ^ C;
              instruction_string = "ASL";
            end
          end

          9'o067: begin // if opcode is TST
            if(B == 1 && (address % 2 == 0)) begin
              Z_Flag = 0;
              N = 0;
              V = 0;
              C = 0;
              if(result[7:0] == 8'b0) begin
                Z_Flag = 1;
              end
              if(result[7:0] < 0) begin
                N = 1;
              end
              instruction_string = "TSTB";
            end
            else if(B == 1 && (address % 2 == 1)) begin
              Z_Flag = 0;
              N = 0;
              V = 0;
              C = 0;
              if(result[15:8] == 8'b0) begin
                Z_Flag = 1;
              end
              if(result[15:8] < 0) begin
                N = 1;
              end
              instruction_string = "TSTB";
            end
            else begin
              Z_Flag = 0;
              N = 0;
              V = 0;
              C = 0;
              if(result == 16'b0) begin
                Z_Flag = 1;
              end
              if(result < 0) begin
                N = 1;
              end
              instruction_string = "TST";
            end
          end
        endcase



        if(regD == 3'h7) begin
          case(modeD)
            3'b010: begin

            end
            3'b011: begin
              memory[instruction] = result;
            end
            3'b110: begin
              memory[PC_read + instruction] = result;
            end
            3'b111: begin
              memory[memory[PC_read + instruction]] = result;
            end
          endcase
        end
        else begin
          case(modeD) // destination mode
            3'b000: begin // register addressing mode
              register[regD] = result[15:0];
              $sformat(regd_string,"R%d", regD);
            end

            3'b001: begin // register deferred addressing mode
              memory[register[regD]] = result[15:0];
              output_out = {2'b01, register[regD]};
              #100;
              $sformat(regd_string,"(R%d)", regD);
            end

            3'b010: begin // auto-increment addressing mode
              memory[register[regD]] = result[15:0];
              output_out = {2'b01, register[regD]};
              #100;
              $sformat(regd_string,"(R%d)+", regD);
              register[regD] = register[regD] + 2 - B;
            end

            3'b011: begin // auto-increment deferred addressing mode
              memory[memory[register[regD]]] = result[15:0];
              //output_out = {2'b01, register[regD]};
              #100;
              output_out = {2'b01, memory[register[regD]]};
              #100;
              $sformat(regd_string,"@(R%d)+", regD);
              register[regD] = register[regD] + 2 - B;
            end

            3'b100: begin // auto-decrement addressing mode
              register[regD] = register[regD] - 2 + B;
              memory[register[regD]] = result[15:0];
              output_out = {2'b01, register[regD]};
              #100;
              $sformat(regd_string,"(R%d)-", regD);
            end

            3'b101: begin // auto-decrement deferred addressing mode
              register[regD] = register[regD] - 2 + B;
              memory[memory[register[regD]]] = result[15:0];
              //output_out = {2'b01, register[regD]};
              #100;
              output_out = {2'b01, memory[register[regD]]};
              #100;
              $sformat(regd_string,"@(R%d)-", regD);
            end
            3'b110: begin
              memory[register[regD] + instruction] = result;
              output_out = {2'b01, register[regD] + instruction};
              $sformat(regd_string,"%o(R%d)", instruction,regD);
              #100;
            end
            3'b111: begin
              memory[memory[register[regD] + instruction]] = result;
              // output_out = {2'b01, register[regD] + instruction};
              #100;
              output_out = {2'b01, memory[register[regD] + instruction]};
              $sformat(regd_string,"@%o(R%d)", instruction,regD);
              #100;
            end
          endcase
        end
        PC = PC + 2;
        next_instruction_flag = 0;
      end

// ----------------------------------------------------------------------- DOUBLE OPERAND

      else if(single_double_flag == 0) begin
      if((modeS == 3'h7 && modeD == 3'h7) || (modeS == 3'h6 && modeD == 3'h6) || (modeS == 3'h7 && modeD == 3'h6) || (modeS == 3'h6 && modeD == 3'h7) || (regS == 3'h7 && regD == 3'h7)) begin
        next_instruction_flag = 2;
        second_instruction = instruction;
        //output_out = {2'b10, PC};
        PC = PC + 2;
      end

      else begin
        instruction_counter = instruction_counter + 1;
        if(regD == 3'h7) begin
          if(old_instruction[15:12] == 4'b1110) begin
            B_bit = 0;
          end
          else begin
            B_bit = B;
          end
          case(modeD)
            3'b010: begin
              valD = instruction;
            end
            3'b011: begin
              output_out = {2'b0, PC};
              #100
              output_out = {2'h0, instruction};
              #100
              valD = memory[instruction];
            end
            3'b110: begin
              output_out = {2'b0, PC};
              #100
              output_out = {2'h0, PC_read + instruction};
              #100
              valD = memory[PC_read + instruction];
            end
            3'b111: begin
              output_out = {2'b0, PC};
              #100
              output_out = {2'h0, PC_read + instruction};
              #100
              output_out = {2'h0, memory[PC_read + instruction]};
              #100
              valD = memory[memory[PC_read + instruction]];
            end
          endcase
        end
        else if(regD != 3'h7) begin
          case(modeD) // source mode
            3'b000: begin // register addressing mode
              valD = register[regD];
              $sformat(regd_string,"R%d", regD);
            end

            3'b001: begin // register deferred addressing mode
              address = register[regD];
              valD = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100;
              $sformat(regd_string,"(R%d)", regD);
            end

            3'b010: begin // auto-increment addressing mode
              address = register[regD];
              valD = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100
              $sformat(regd_string,"(R%d)+", regD);
            end

            3'b011: begin // auto-increment deferred addressing mode
              address = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100
              valD = memory[memory[register[regD]]];
              output_out = {2'b0, memory[register[regD]]};
              #100
              $sformat(regd_string,"@(R%d)+", regD);
            end

            3'b100: begin // auto-decrement addressing mode
              address = register[regD];
              valD = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100;
              $sformat(regd_string,"-(R%d)", regD);
            end

            3'b101: begin // auto-decrement deferred addressing mode
              valD = memory[memory[register[regD]]];
              address = memory[register[regD]];
              output_out = {2'b0, register[regD]};
              #100
              output_out = {2'b0, memory[register[regD]]};
              #100;
              $sformat(regd_string,"@-(R%d)", regD);
            end

            3'b110: begin
              output_out = {2'b0, register[regD] + instruction};
              #100
              $sformat(regd_string,"%o(R%d)", instruction,regD);
              valD = memory[register[regD] + instruction];
            end

            3'b111: begin
              output_out = {2'b0, register[regD] + instruction};
              #100
              output_out = {2'b0, memory[register[regD] + instruction]};
              #100
              $sformat(regd_string,"@%o(R%d)", instruction,regD);
              valD = memory[memory[register[regD] + instruction]];
            end
          endcase
        end

        if(opcodeD != 3'h7) begin
        if(regS == 3'h7) begin
          case(modeS)
            3'b010: begin
              valS = instruction;
              $sformat(regs_string,"#%o", instruction);
              output_out = {2'h0, PC};
              #100;
            end
            3'b011: begin
              output_out = {2'b0, PC};
              #100
              output_out = {2'h0, instruction};
              #100
              valS = memory[instruction];
              if(instruction >= PC_start) begin
                $sformat(regs_string,"@#%o", instruction);
              end
              else begin
                $sformat(regs_string,"%o", memory[instruction]);
              end
            end
            3'b110: begin
              output_out = {2'b0, PC};
              #100
              output_out = {2'h0, PC_read + instruction};
              #100
              valS = memory[PC_read + instruction];
              if(instruction + PC_read >= PC_start) begin
                $sformat(regs_string,"%o", instruction);
              end
              else begin
                $sformat(regs_string,"%o", memory[PC_read + instruction]);
              end
            end
            3'b111: begin
              valS = memory[memory[PC_read + instruction]];
              output_out = {2'b0, PC};
              #100
              output_out = {2'h0, PC_read + instruction};
              #100;
              output_out = {2'h0, memory[PC_read + instruction]};
              #100;
              if(instruction + PC_read >= PC_start) begin
                $sformat(regs_string,"@%o", instruction);
              end
              else begin
                $sformat(regs_string,"%o", memory[memory[PC_read + instruction]]);
              end
            end
          endcase

        end
        else if(regS != 3'h7) begin
          case(modeS) // source mode
            3'b000: begin // register addressing mode
              valS = register[regS];
              $sformat(regs_string,"R%d", regS);
            end

            3'b001: begin // register deferred addressing mode
              valS = memory[register[regS]];
              output_out = {2'b0, register[regS]};
              #100;
              $sformat(regs_string,"(R%d)", regS);
            end

            3'b010: begin // auto-increment addressing mode
              valS = memory[register[regS]];
              output_out = {2'b0, register[regS]};
              #100;
              register[regS] = register[regS] + 2 - B_bit;
              $sformat(regs_string,"(R%d)+", regS);
            end

            3'b011: begin // auto-increment deferred addressing mode
              valS = memory[memory[register[regS]]];
              output_out = {2'b0, register[regS]};
              #100;
              output_out = {2'b0, memory[register[regS]]};
              #100;
              register[regS] = register[regS] + 2 - B_bit;
              $sformat(regs_string,"@(R%d)+", regS);
            end

            3'b100: begin // auto-decrement addressing mode
              register[regS] = register[regS] - 2 + B_bit;
              valS = memory[register[regS]];
              output_out = {2'b0, register[regS]};
              #100;
              $sformat(regs_string,"-(R%d)", regS);
            end

            3'b101: begin // auto-decrement deferred addressing mode
              register[regS] = register[regS] - 2 + B_bit;
              valS = memory[memory[register[regS]]];
              output_out = {2'b0, register[regS]};
              #100;
              output_out = {2'b0, memory[register[regS]]};
              #100;
              $sformat(regs_string,"@-(R%d)", regS);
            end
            3'b110: begin
              output_out = {2'b0, register[regS] + instruction};
              #100
              $sformat(regs_string,"%o(R%d)", instruction,regS);
              valS = memory[register[regS] + instruction];
            end
            3'b111: begin
              valS = memory[memory[register[regS] + instruction]];
              output_out = {2'b0, register[regS] + instruction};
              #100
              $sformat(regs_string,"@%o(R%d)", instruction,regS);
              output_out = {2'b0, memory[register[regS] + instruction]};
              #100;
            end
          endcase
        end
        end

        // COPY OF DOUBLE OPERAND INSTRUCTIONS HERE
        case(opcodeD)
          3'b001: begin // if opcode is MOV
            if(B == 1) begin
              result = valS;
              result[15:8] = {8{valS[7]}};
              N = 0;
              Z_Flag = 0;
              if(result == 16'b0) begin
                Z_Flag = 1;
              end
              V = 0;
              if(result < 0) begin
                N = 1;
                Z_Flag = 0;
              end
              instruction_string = "MOVB";
            end
            else begin
              result = valS;
              N = 0;
              Z_Flag = 0;
              if(result == 16'b0) begin
                Z_Flag = 1;
              end
              V = 0;
              if(result < 0) begin
                N = 1;
                Z_Flag = 0;
              end
              instruction_string = "MOV";
            end
          end

          3'b010: begin // if opcode is CMP
            if(B == 1 && (address % 2 == 0)) begin
              result_temp[7:0] = valS[7:0] - valD[7:0];
              Z_Flag = 0;
              N = 0;
              V = 0;
              C = 1;
              if(result_temp[7:0] == 8'b0) begin
                Z_Flag = 1;
              end
              if(result_temp[7:0] < 0) begin
                N = 1;
              end
              instruction_string = "CMPB";
            end
            else if(B == 1 && (address % 2 == 1)) begin
              result_temp[15:8] = valS[15:8] - valD[15:8];
              Z_Flag = 0;
              N = 0;
              V = 0;
              C = 1;
              if(result_temp[15:8] == 8'b0) begin
                Z_Flag = 1;
              end
              if(result_temp[15:8] < 0) begin
                N = 1;
              end
              instruction_string = "CMPB";
            end
            else begin
              result_temp = valS - valD;
              Z_Flag = 0;
              N = 0;
              V = 0;
              C = 1;
              if(result_temp == 16'b0) begin
                Z_Flag = 1;
              end
              if(result_temp < 0) begin
                N = 1;
              end
              instruction_string = "CMP";
            end
          end

          3'b110: begin // if opcode is ADD/SUB
            if(B == 0) begin // if opcode is ADD
                result = valD + valS;
                C = valD[15] & valS[15];
                N = 0;
                Z_Flag = 0;
                V = 0;
                if(result == 17'b0) begin
                  Z_Flag = 1;
                end
                if(result < 0) begin
                  N = 1;
                end
                instruction_string = "ADD";
            end
            else if(B == 1) begin // if opcode is SUB
              result = valD - valS;
              C = 1;
              N = 0;
              Z_Flag = 0;
              V = 0;
              if(result == 17'b0) begin
                Z_Flag = 1;
              end
              if(result < 0) begin
                N = 1;
              end
              instruction_string = "SUB";
            end
          end

          3'b011: begin // if opcode is BIT
            if(B == 1 && (address % 2 == 0)) begin
              result_temp[7:0] = valS[7:0] & valD[7:0];
              Z_Flag = 0;
              V = 0;
              N = result_temp[7];
              if(result_temp[7:0] == 8'b0) begin
                Z_Flag = 1;
              end
              instruction_string = "BITB";
            end
            else if(B == 1 && (address % 2 == 1)) begin
              result_temp[15:8] = valS[15:8] & valD[15:8];
              Z_Flag = 0;
              V = 0;
              N = result_temp[15];
              if(result_temp[15:8] == 8'b0) begin
                Z_Flag = 1;
              end
              instruction_string = "BITB";
            end
            else begin
              result_temp = valS & valD;
              Z_Flag = 0;
              V = 0;
              N = result_temp[15];
              if(result_temp == 17'b0) begin
                Z_Flag = 1;
              end
              instruction_string = "BIT";
            end


          end

          3'b100: begin // if opcode is BIC
            if(B == 1 && (address % 2 == 0)) begin
              result[7:0] = ~(valS[7:0]) & valD[7:0];
              Z_Flag = 0;
              V = 0;
              N = result[7];
              if(result[7:0] == 8'b0) begin
                Z_Flag = 1;
              end
              instruction_string = "BICB";
            end
            else if(B == 1 && (address % 2 == 1)) begin
              result[15:8] = ~(valS[15:8]) & valD[15:8];
              Z_Flag = 0;
              V = 0;
              N = result[15];
              if(result[15:8] == 8'b0) begin
                Z_Flag = 1;
              end
              instruction_string = "BICB";
            end
            else begin
              result = ~(valS) & valD;
              N = result[15];
              Z_Flag = 0;
              V = 0;
              if(result == 16'b0) begin
                Z_Flag = 1;
              end
              instruction_string = "BIC";
            end

          end

          3'b101: begin // if opcode is BIS
            if(B == 1 && (address % 2 == 0)) begin
              result[7:0] = valS[7:0] | valD[7:0];
              Z_Flag = 0;
              V = 0;
              N = result[7];
              if(result[7:0] == 8'b0) begin
                Z_Flag = 1;
              end
              instruction_string = "BISB";
            end
            else if(B == 1 && (address % 2 == 1)) begin
              result[15:8] = valS[15:8] | valD[15:8];
              Z_Flag = 0;
              V = 0;
              N = result[15];
              if(result[15:8] == 8'b0) begin
                Z_Flag = 1;
              end
              instruction_string = "BISB";
            end
            else begin
              result = valS | valD;
              N = result[15];
              Z_Flag = 0;
              V = 0;
              if(result == 16'b0) begin
                Z_Flag = 1;
              end
              instruction_string = "BIS";
            end
          end

          3'b111: begin // if opcode is MUL/DIV/ASH/ASHC/XOR

            if(regD == 3'h7) begin
              case(modeD)
                3'b010: begin
                  $sformat(regs_string,"#%o", instruction);
                end
                3'b011: begin
                  $sformat(regs_string,"@#%o", instruction);
                end
                3'b110: begin
                  $sformat(regs_string,"%o", instruction);
                end
                3'b111: begin
                  $sformat(regs_string,"@%o", instruction);
                end
              endcase
            end
            else if(regD != 3'h7) begin
              case(modeD) // source mode
                3'b000: begin // register addressing mode
                  $sformat(regs_string,"R%d", regD);
                end

                3'b001: begin // register deferred addressing mode
                  $sformat(regs_string,"(R%d)", regD);
                end

                3'b010: begin // auto-increment addressing mode
                  $sformat(regs_string,"(R%d)+", regD);
                end

                3'b011: begin // auto-increment deferred addressing mode
                  $sformat(regs_string,"@(R%d)+", regD);
                end

                3'b100: begin // auto-decrement addressing mode
                  $sformat(regs_string,"-(R%d)", regD);
                end

                3'b101: begin // auto-decrement deferred addressing mode
                  $sformat(regs_string,"@-(R%d)", regD);
                end

                3'b110: begin
                  $sformat(regs_string,"%o(R%d)", instruction,regD);
                end

                3'b111: begin
                  $sformat(regs_string,"@%o(R%d)", instruction,regD);
                end
              endcase
            end

            case(modeS)
              3'b000: begin // if opcode is MUL
                instruction_string = "MUL";
                $sformat(regd_string,"R%d", regS);
                mul_result = register[regS] * valD;
                V = 0;
                N = 0;
                Z_Flag = 0;
                if(regS % 2 == 0) begin
                  register[regS] = mul_result[31:16];
                  result = mul_result[31:16];
                  register[regS + 1] = mul_result[15:0];
                end
                else begin
                  result = mul_result[31:16];
                  register[regS] = mul_result[15:0];
                end
                if(mul_result < -32768 || mul_result > 32767) begin
                  C = 1;
                end
                if(mul_result == 32'b0) begin
                  Z_Flag = 1;
                end
                if(mul_result < 0) begin
                  N = 1;
                end
              end

              3'b001: begin // if opcode is DIV
                remainder = register[regS] % valD;
                register[regS] = register[regS] - remainder;
                register[regS] = register[regS]/valD;
                register[regS+1] = remainder;
                N = 0;
                Z_Flag = 0;
                C = 0;
                if(register[regS] < 0) begin
                  N = 1;
                end
                else if(register[regS] == 0) begin
                  Z_Flag = 1;
                end
                else if(valD == 0) begin
                  V = 1;
                  C = 1;
                end
                instruction_string = "DIV";
                $sformat(regd_string,"R%d", regS);
              end

              3'b010: begin // if opcode is ASH
                shift = instruction[5:0];
                result = register[regS];
                Z_Flag = 0;
                N = 0;
                V = 0;
                if(shift < 0) begin
                  C = result[0];
                end
                else begin
                  C = result[15];
                end
                register[regS] = result >> shift;
                if(register[regS] == 16'b0) begin
                  Z_Flag = 1;
                end
                if(register[regS] < 0) begin
                  N = 1;
                end
                if(result[15] != register[regS][15]) begin
                  V = 1;
                end
                instruction_string = "ASH";
                $sformat(regd_string,"R%d", regS);
              end

              3'b011: begin // if opcode is ASHC
                instruction_string = "ASHC";
                $sformat(regd_string,"R%d", regS);
                if(regS % 2 == 0) begin
                  mul_result = {register[regS], register[regS+1]};
                  mul_result = mul_result >> old_instruction[5:0];
                  Z_Flag = 0;
                  N = 0;
                  V = 0;
                  if(old_instruction[5] == 1) begin
                    C = register[regS][15];
                  end
                  if(old_instruction[5] == 0) begin
                    C = register[regS+1][0];
                  end
                  if(mul_result < 0) begin
                    N = 1;
                  end
                  if(mul_result == 32'b0) begin
                    Z_Flag = 1;
                  end
                  if(mul_result[31] != register[regS][15]) begin
                    V = 1;
                  end
                  register[regS] = mul_result[31:16];
                  register[regS + 1] = mul_result[15:0];
                end
                else begin
                  mul_result = {register[regS-1], register[regS]};
                  mul_result = mul_result >> old_instruction[5:0];
                  Z_Flag = 0;
                  N = 0;
                  V = 0;
                  if(old_instruction[5] == 1) begin
                    C = register[regS-1][15];
                  end
                  if(old_instruction[5] == 0) begin
                    C = register[regS][0];
                  end
                  if(mul_result < 0) begin
                    N = 1;
                  end
                  if(mul_result == 32'b0) begin
                    Z_Flag = 1;
                  end
                  if(mul_result[31] != register[regS-1][15]) begin
                    V = 1;
                  end
                  register[regS-1] = mul_result[31:16];
                  register[regS] = mul_result[15:0];
                end
              end

              3'b100: begin // if opcode is XOR
                result = valD ^ register[regS];
                N = 0;
                Z_Flag = 0;
                V = 0;
                if(result == 17'b0) begin
                  Z_Flag = 1;
                end
                if(result < 0) begin
                  N = 1;
                end
                instruction_string = "XOR";
                $sformat(regd_string,"R%d", regS);
              end
            endcase
          end
        endcase

        if({opcodeD, modeS} != 6'o70 || {opcodeD, modeS} != 6'o71 || {opcodeD, modeS} != 6'o72 || {opcodeD, modeS} != 6'o73) begin
        if(regD == 3'h7) begin
          case(modeD)
            3'b010: begin

            end
            3'b011: begin
              memory[instruction] = result;
              output_out = {2'b01, instruction};
              #100;
            end
            3'b110: begin
              memory[PC_read + instruction] = result;
              output_out = {2'b01, PC_read + instruction};
              #100;
            end
            3'b111: begin
              memory[memory[PC_read + instruction]] = result;
              //output_out = {2'b01, PC_read + instruction};
              #100;
              output_out = {2'b01, memory[PC_read + instruction]};
              #100;
            end
          endcase
        end
        else if(regD != 3'h7) begin
          case(modeD) // destination mode
            3'b000: begin // register addressing mode
              register[regD] = result[15:0];
            end

            3'b001: begin // register deferred addressing mode
              memory[register[regD]] = result[15:0];
              output_out = {2'b01, register[regD]};
              #100;
            end

            3'b010: begin // auto-increment addressing mode
              memory[register[regD]] = result[15:0];
              output_out = {2'b01, register[regD]};
              #100;
              register[regD] = register[regD] + 2 - B_bit;
            end

            3'b011: begin // auto-increment deferred addressing mode
              memory[memory[register[regD]]] = result[15:0];
              //output_out = {2'b01, register[regD]};
              #100;
              output_out = {2'b01, memory[register[regD]]};
              #100;
              register[regD] = register[regD] + 2 - B_bit;
            end

            3'b100: begin // auto-decrement addressing mode
              register[regD] = register[regD] - 2 + B_bit;
              memory[register[regD]] = result[15:0];
              output_out = {2'b01, register[regD]};
              #100;
            end

            3'b101: begin // auto-decrement deferred addressing mode
              register[regD] = register[regD] - 2 + B_bit;
              memory[memory[register[regD]]] = result[15:0];
              //output_out = {2'b01, register[regD]};
              #100;
              output_out = {2'b01, memory[register[regD]]};
              #100;
            end
            3'b110: begin
              memory[register[regD] + instruction] = result;
              output_out = {2'b01, register[regD] + instruction};
              #100;
            end
            3'b111: begin
              memory[memory[register[regD] + instruction]] = result;
              //output_out = {2'b01, register[regD] + instruction};
              #100;
              output_out = {2'b01, memory[register[regD] + instruction]};
              #100;
            end
          endcase
        end
        end
        PC = PC + 2;
        next_instruction_flag = 0;
        end

      end


    end

    else if(next_instruction_flag == 2) begin
      memory[PC] = instruction;
      PC_read = PC + 2;
      instruction_counter = instruction_counter + 1;
      if(opcodeD != 3'h7) begin
      if(regS == 3'h7) begin
        case(modeS)
          3'b010: begin
            valS = second_instruction;
            $sformat(regs_string,"#%o", second_instruction);
          end
          3'b011: begin
            output_out = {2'b0, PC};
            #100
            output_out = {2'h0, second_instruction};
            #100
            valS = memory[second_instruction];
            if(second_instruction >= PC_start) begin
              $sformat(regs_string,"@#%o", second_instruction);
            end
            else begin
              $sformat(regs_string,"%o", memory[second_instruction]);
            end
          end
          3'b110: begin
            output_out = {2'b0, PC};
            #100
            output_out = {2'h0, PC_read - 2 + second_instruction};
            #100
            valS = memory[PC_read - 2 + second_instruction];
            if(second_instruction + PC_read - 2 >= PC_start) begin
              $sformat(regs_string,"%o", second_instruction);
            end
            else begin
              $sformat(regs_string,"%o", memory[PC_read - 2 + second_instruction]);
            end
          end
          3'b111: begin
            valS = memory[memory[PC_read - 2 + second_instruction]];
            output_out = {2'b0, PC};
            #100
            output_out = {2'h0, PC_read - 2 + second_instruction};
            #100;
            output_out = {2'h0, memory[PC_read - 2 + second_instruction]};
            #100;
            if(second_instruction + PC_read >= PC_start) begin
              $sformat(regs_string,"@%o", second_instruction);
            end
            else begin
              $sformat(regs_string,"%o", memory[memory[PC_read - 2 + second_instruction]]);
            end
          end
        endcase

      end
      else if(regS != 3'h7) begin
        case(modeS) // source mode
          3'b110: begin
            output_out = {2'b0, register[regS] + second_instruction};
            #100
            $sformat(regs_string,"%o(R%d)", second_instruction,regS);
            valS = memory[register[regS] + second_instruction];
          end
          3'b111: begin
            valS = memory[memory[register[regS] + second_instruction]];
            output_out = {2'b0, register[regS] + second_instruction};
            #100
            $sformat(regs_string,"@%o(R%d)", second_instruction,regS);
            output_out = {2'b0, memory[register[regS] + second_instruction]};
            #100;
          end
        endcase
      end
      end

      if(regD == 3'h7) begin
        case(modeD)
          3'b010: begin
            valD = instruction;
          end
          3'b011: begin
            output_out = {2'b0, PC};
            #100
            output_out = {2'h0, instruction};
            #100
            valD = memory[instruction];
          end
          3'b110: begin
            output_out = {2'b0, PC};
            #100
            output_out = {2'h0, PC_read + instruction};
            #100
            valD = memory[PC_read + instruction];
            if(instruction + PC_read >= PC_start) begin
              $sformat(regd_string,"%o", instruction);
            end
            else begin
              $sformat(regd_string,"%o", memory[PC_read + instruction]);
            end
          end
          3'b111: begin
            valD = memory[memory[PC_read + instruction]];
            output_out = {2'b0, PC};
            #100
            output_out = {2'h0, PC_read + instruction};
            #100;
            output_out = {2'h0, memory[PC_read + instruction]};
            #100;
            if(instruction + PC_read >= PC_start) begin
              $sformat(regd_string,"@%o", instruction);
            end
            else begin
              $sformat(regd_string,"%o", memory[memory[PC_read + instruction]]);
            end
          end
        endcase

      end
      else if(regD != 3'h7) begin
        case(modeD) // source mode
          3'b110: begin
            output_out = {2'b0, register[regD] + instruction};
            #100
            $sformat(regd_string,"%o(R%d)", instruction,regD);
            valD = memory[register[regD] + instruction];
          end
          3'b111: begin
            valD = memory[memory[register[regD] + instruction]];
            output_out = {2'b0, register[regD] + instruction};
            #100
            $sformat(regd_string,"@%o(R%d)", instruction,regD);
            output_out = {2'b0, memory[register[regD] + instruction]};
            #100;
          end
        endcase
      end

      case(opcodeD)
        3'b001: begin // if opcode is MOV
          if(B == 1) begin
            result = valS;
            result[15:8] = {8{valS[7]}};
            N = 0;
            Z_Flag = 0;
            if(result == 16'b0) begin
              Z_Flag = 1;
            end
            V = 0;
            if(result < 0) begin
              N = 1;
              Z_Flag = 0;
            end
            instruction_string = "MOVB";
          end
          else begin
            result = valS;
            N = 0;
            Z_Flag = 0;
            if(result == 16'b0) begin
              Z_Flag = 1;
            end
            V = 0;
            if(result < 0) begin
              N = 1;
              Z_Flag = 0;
            end
            instruction_string = "MOV";
          end
        end

        3'b010: begin // if opcode is CMP
          if(B == 1 && (address % 2 == 0)) begin
            result_temp[7:0] = valS[7:0] - valD[7:0];
            Z_Flag = 0;
            N = 0;
            V = 0;
            C = 1;
            if(result_temp[7:0] == 8'b0) begin
              Z_Flag = 1;
            end
            if(result_temp[7:0] < 0) begin
              N = 1;
            end
            instruction_string = "CMPB";
          end
          else if(B == 1 && (address % 2 == 1)) begin
            result_temp[15:8] = valS[15:8] - valD[15:8];
            Z_Flag = 0;
            N = 0;
            V = 0;
            C = 1;
            if(result_temp[15:8] == 8'b0) begin
              Z_Flag = 1;
            end
            if(result_temp[15:8] < 0) begin
              N = 1;
            end
            instruction_string = "CMPB";
          end
          else begin
            result_temp = valS - valD;
            Z_Flag = 0;
            N = 0;
            V = 0;
            C = 1;
            if(result_temp == 16'b0) begin
              Z_Flag = 1;
            end
            if(result_temp < 0) begin
              N = 1;
            end
            instruction_string = "CMP";
          end
        end

        3'b110: begin // if opcode is ADD/SUB
          if(B == 0) begin // if opcode is ADD
              result = valD + valS;
              C = valD[15] & valS[15];
              N = 0;
              Z_Flag = 0;
              V = 0;
              if(result == 17'b0) begin
                Z_Flag = 1;
              end
              if(result < 0) begin
                N = 1;
              end
              instruction_string = "ADD";
          end
          else if(B == 1) begin // if opcode is SUB
            result = valD - valS;
            C = 1;
            N = 0;
            Z_Flag = 0;
            V = 0;
            if(result == 17'b0) begin
              Z_Flag = 1;
            end
            if(result < 0) begin
              N = 1;
            end
            instruction_string = "SUB";
          end
        end

        3'b011: begin // if opcode is BIT
          if(B == 1 && (address % 2 == 0)) begin
            result_temp[7:0] = valS[7:0] & valD[7:0];
            Z_Flag = 0;
            V = 0;
            N = result_temp[7];
            if(result_temp[7:0] == 8'b0) begin
              Z_Flag = 1;
            end
            instruction_string = "BITB";
          end
          else if(B == 1 && (address % 2 == 1)) begin
            result_temp[15:8] = valS[15:8] & valD[15:8];
            Z_Flag = 0;
            V = 0;
            N = result_temp[15];
            if(result_temp[15:8] == 8'b0) begin
              Z_Flag = 1;
            end
            instruction_string = "BITB";
          end
          else begin
            result_temp = valS & valD;
            Z_Flag = 0;
            V = 0;
            N = result_temp[15];
            if(result_temp == 17'b0) begin
              Z_Flag = 1;
            end
            instruction_string = "BIT";
          end


        end

        3'b100: begin // if opcode is BIC
          if(B == 1 && (address % 2 == 0)) begin
            result[7:0] = ~(valS[7:0]) & valD[7:0];
            Z_Flag = 0;
            V = 0;
            N = result[7];
            if(result[7:0] == 8'b0) begin
              Z_Flag = 1;
            end
            instruction_string = "BICB";
          end
          else if(B == 1 && (address % 2 == 1)) begin
            result[15:8] = ~(valS[15:8]) & valD[15:8];
            Z_Flag = 0;
            V = 0;
            N = result[15];
            if(result[15:8] == 8'b0) begin
              Z_Flag = 1;
            end
            instruction_string = "BICB";
          end
          else begin
            result = ~(valS) & valD;
            N = result[15];
            Z_Flag = 0;
            V = 0;
            if(result == 16'b0) begin
              Z_Flag = 1;
            end
            instruction_string = "BIC";
          end

        end

        3'b101: begin // if opcode is BIS
          if(B == 1 && (address % 2 == 0)) begin
            result[7:0] = valS[7:0] | valD[7:0];
            Z_Flag = 0;
            V = 0;
            N = result[7];
            if(result[7:0] == 8'b0) begin
              Z_Flag = 1;
            end
            instruction_string = "BISB";
          end
          else if(B == 1 && (address % 2 == 1)) begin
            result[15:8] = valS[15:8] | valD[15:8];
            Z_Flag = 0;
            V = 0;
            N = result[15];
            if(result[15:8] == 8'b0) begin
              Z_Flag = 1;
            end
            instruction_string = "BISB";
          end
          else begin
            result = valS | valD;
            N = result[15];
            Z_Flag = 0;
            V = 0;
            if(result == 16'b0) begin
              Z_Flag = 1;
            end
            instruction_string = "BIS";
          end
        end

        3'b111: begin // if opcode is MUL/DIV/ASH/ASHC/XOR

          if(regD == 3'h7) begin
            case(modeD)
              3'b010: begin
                $sformat(regs_string,"#%o", instruction);
              end
              3'b011: begin
                $sformat(regs_string,"@#%o", instruction);
              end
              3'b110: begin
                $sformat(regs_string,"%o", instruction);
              end
              3'b111: begin
                $sformat(regs_string,"@%o", instruction);
              end
            endcase
          end
          else if(regD != 3'h7) begin
            case(modeD) // source mode
              3'b000: begin // register addressing mode
                $sformat(regs_string,"R%d", regD);
              end

              3'b001: begin // register deferred addressing mode
                $sformat(regs_string,"(R%d)", regD);
              end

              3'b010: begin // auto-increment addressing mode
                $sformat(regs_string,"(R%d)+", regD);
              end

              3'b011: begin // auto-increment deferred addressing mode
                $sformat(regs_string,"@(R%d)+", regD);
              end

              3'b100: begin // auto-decrement addressing mode
                $sformat(regs_string,"-(R%d)", regD);
              end

              3'b101: begin // auto-decrement deferred addressing mode
                $sformat(regs_string,"@-(R%d)", regD);
              end

              3'b110: begin
                $sformat(regs_string,"%o(R%d)", instruction,regD);
              end

              3'b111: begin
                $sformat(regs_string,"@%o(R%d)", instruction,regD);
              end
            endcase
          end

          case(modeS)
            3'b000: begin // if opcode is MUL
              instruction_string = "MUL";
              $sformat(regd_string,"R%d", regS);
              mul_result = register[regS] * valD;
              V = 0;
              N = 0;
              Z_Flag = 0;
              if(regS % 2 == 0) begin
                register[regS] = mul_result[31:16];
                result = mul_result[31:16];
                register[regS + 1] = mul_result[15:0];
              end
              else begin
                result = mul_result[31:16];
                register[regS] = mul_result[15:0];
              end
              if(mul_result < -32768 || mul_result > 32767) begin
                C = 1;
              end
              if(mul_result == 32'b0) begin
                Z_Flag = 1;
              end
              if(mul_result < 0) begin
                N = 1;
              end
            end

            3'b001: begin // if opcode is DIV
              remainder = register[regS] % valD;
              register[regS] = register[regS] - remainder;
              register[regS] = register[regS]/valD;
              register[regS+1] = remainder;
              N = 0;
              Z_Flag = 0;
              C = 0;
              if(register[regS] < 0) begin
                N = 1;
              end
              else if(register[regS] == 0) begin
                Z_Flag = 1;
              end
              else if(valD == 0) begin
                V = 1;
                C = 1;
              end
              instruction_string = "DIV";
              $sformat(regd_string,"R%d", regS);
            end

            3'b010: begin // if opcode is ASH
              shift = instruction[5:0];
              result = register[regS];
              Z_Flag = 0;
              N = 0;
              V = 0;
              if(shift < 0) begin
                C = result[0];
              end
              else begin
                C = result[15];
              end
              register[regS] = result >> shift;
              if(register[regS] == 16'b0) begin
                Z_Flag = 1;
              end
              if(register[regS] < 0) begin
                N = 1;
              end
              if(result[15] != register[regS][15]) begin
                V = 1;
              end
              instruction_string = "ASH";
              $sformat(regd_string,"R%d", regS);
            end

            3'b011: begin // if opcode is ASHC
              instruction_string = "ASHC";
              $sformat(regd_string,"R%d", regS);
              if(regS % 2 == 0) begin
                mul_result = {register[regS], register[regS+1]};
                mul_result = mul_result >> old_instruction[5:0];
                Z_Flag = 0;
                N = 0;
                V = 0;
                if(old_instruction[5] == 1) begin
                  C = register[regS][15];
                end
                if(old_instruction[5] == 0) begin
                  C = register[regS+1][0];
                end
                if(mul_result < 0) begin
                  N = 1;
                end
                if(mul_result == 32'b0) begin
                  Z_Flag = 1;
                end
                if(mul_result[31] != register[regS][15]) begin
                  V = 1;
                end
                register[regS] = mul_result[31:16];
                register[regS + 1] = mul_result[15:0];
              end
              else begin
                mul_result = {register[regS-1], register[regS]};
                mul_result = mul_result >> old_instruction[5:0];
                Z_Flag = 0;
                N = 0;
                V = 0;
                if(old_instruction[5] == 1) begin
                  C = register[regS-1][15];
                end
                if(old_instruction[5] == 0) begin
                  C = register[regS][0];
                end
                if(mul_result < 0) begin
                  N = 1;
                end
                if(mul_result == 32'b0) begin
                  Z_Flag = 1;
                end
                if(mul_result[31] != register[regS-1][15]) begin
                  V = 1;
                end
                register[regS-1] = mul_result[31:16];
                register[regS] = mul_result[15:0];
              end
            end

            3'b100: begin // if opcode is XOR
              result = valD ^ register[regS];
              N = 0;
              Z_Flag = 0;
              V = 0;
              if(result == 17'b0) begin
                Z_Flag = 1;
              end
              if(result < 0) begin
                N = 1;
              end
              instruction_string = "XOR";
              $sformat(regd_string,"R%d", regS);
            end
          endcase
        end
      endcase

      if({opcodeD, modeS} != 6'o70 || {opcodeD, modeS} != 6'o71 || {opcodeD, modeS} != 6'o72 || {opcodeD, modeS} != 6'o73) begin
      if(regD == 3'h7) begin
        case(modeD)
          3'b010: begin

          end
          3'b011: begin
            memory[instruction] = result;
            output_out = {2'b01, instruction};
            #100;
          end
          3'b110: begin
            memory[PC_read + instruction] = result;
            output_out = {2'b01, PC_read + instruction};
            #100;
          end
          3'b111: begin
            memory[memory[PC_read + instruction]] = result;
            output_out = {2'b01, PC_read + instruction};
            #100;
            output_out = {2'b01, memory[PC_read + instruction]};
            #100;
          end
        endcase
      end
      else if(regD != 3'h7) begin
        case(modeD) // destination mode
          3'b000: begin // register addressing mode
            register[regD] = result[15:0];
          end

          3'b001: begin // register deferred addressing mode
            memory[register[regD]] = result[15:0];
            output_out = {2'b01, register[regD]};
            #100;
          end

          3'b010: begin // auto-increment addressing mode
            memory[register[regD]] = result[15:0];
            output_out = {2'b01, register[regD]};
            #100;
            register[regD] = register[regD] + 2 - B_bit;
          end

          3'b011: begin // auto-increment deferred addressing mode
            memory[memory[register[regD]]] = result[15:0];
            output_out = {2'b01, register[regD]};
            #100;
            output_out = {2'b01, memory[register[regD]]};
            #100;
            register[regD] = register[regD] + 2 - B_bit;
          end

          3'b100: begin // auto-decrement addressing mode
            register[regD] = register[regD] - 2 + B_bit;
            memory[register[regD]] = result[15:0];
            output_out = {2'b01, register[regD]};
            #100;
          end

          3'b101: begin // auto-decrement deferred addressing mode
            register[regD] = register[regD] - 2 + B_bit;
            memory[memory[register[regD]]] = result[15:0];
            output_out = {2'b01, register[regD]};
            #100;
            output_out = {2'b01, memory[register[regD]]};
            #100;
          end
          3'b110: begin
            memory[register[regD] + instruction] = result;
            output_out = {2'b01, register[regD] + instruction};
            #100;
          end
          3'b111: begin
            memory[memory[register[regD] + instruction]] = result;
            output_out = {2'b01, register[regD] + instruction};
            #100;
            output_out = {2'b01, memory[register[regD] + instruction]};
            #100;
          end
        endcase
      end
      end
      PC = PC + 2;
      next_instruction_flag = 0;
    end

  end

reg0 = register[0];
reg1 = register[1];
reg2 = register[2];
reg3 = register[3];
reg4 = register[4];
reg5 = register[5];
reg6 = register[6];
reg7 = PC;
NZVC = {N,Z_Flag,V,C};
instruction_type = single_double_flag;
instruction_num = instruction_counter;

end

endmodule
