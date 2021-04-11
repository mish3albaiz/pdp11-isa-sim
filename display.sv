// address_sort.sv - ECE586 Final Project - PDP Simulator Testbench
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
//
//__________________________________________________________________________________________

module display(mode, instruction_string, registers_val, registerD, registerS, flags, num_instructions, instruction_type);

input bit mode;
input string instruction_string, registerD, registerS;
input logic [127:0] registers_val;
input [3:0] flags;
input [63:0] num_instructions;
input logic [1:0] instruction_type; // 1 = single, 0 = double, 2 = branch
logic signed [15:0] reg7;
always @(num_instructions) begin
  reg7 = registers_val[127:112];
  // halt operand display
  if(mode == 1 && instruction_string == "HALT")begin
  $display("Current Instruction: %0s", instruction_string);
  $display("N Flag: %o | Z Flag: %o | V Flag: %o | C Flag: %o", flags[3], flags[2], flags[1], flags[0]);
  $display("R7: %o | R6: %o | R5: %o | R4: %o | R3: %o | R2: %o | R1: %o | R0: %o",reg7, registers_val[111:96], registers_val[95:80], registers_val[79:64], registers_val[63:48], registers_val[47:32], registers_val[31:16], registers_val[15:0]);
  $display("_____________________________________________________________________________________________________________________________________________");
  $display("SIMULATION COMPLETE");
  $display("Total Instructions Executed: %0d", num_instructions);
  #100;
  $stop;
  end
  // double operand display
  else if(mode == 1 && instruction_type == 2'b00)begin
  $display("Current Instruction: %0s %0s, %0s", instruction_string, registerS, registerD);
  $display("N Flag: %o | Z Flag: %o | V Flag: %o | C Flag: %o", flags[3], flags[2], flags[1], flags[0]);
  $display("R7: %o | R6: %o | R5: %o | R4: %o | R3: %o | R2: %o | R1: %o | R0: %o",registers_val[127:112] - 2'b10, registers_val[111:96], registers_val[95:80], registers_val[79:64], registers_val[63:48], registers_val[47:32], registers_val[31:16], registers_val[15:0]);
  $display("_____________________________________________________________________________________________________________________________________________");
  end
  // single operand display
  else if(mode == 1 && instruction_type == 2'b01)begin
  $display("Current Instruction: %0s %0s", instruction_string, registerD);
  $display("N Flag: %o | Z Flag: %o | V Flag: %o | C Flag: %o", flags[3], flags[2], flags[1], flags[0]);
  $display("R7: %o | R6: %o | R5: %o | R4: %o | R3: %o | R2: %o | R1: %o | R0: %o",registers_val[127:112] - 2'b10, registers_val[111:96], registers_val[95:80], registers_val[79:64], registers_val[63:48], registers_val[47:32], registers_val[31:16], registers_val[15:0]);
  $display("_____________________________________________________________________________________________________________________________________________");
  end
  // branch operand display
  else if(mode == 1 && instruction_type == 2'b10)begin
  $display("Current Instruction: %0s", instruction_string);
  $display("N Flag: %o | Z Flag: %o | V Flag: %o | C Flag: %o", flags[3], flags[2], flags[1], flags[0]);
  $display("R7: %o | R6: %o | R5: %o | R4: %o | R3: %o | R2: %o | R1: %o | R0: %o",registers_val[127:112] - 2'b10, registers_val[111:96], registers_val[95:80], registers_val[79:64], registers_val[63:48], registers_val[47:32], registers_val[31:16], registers_val[15:0]);
  $display("_____________________________________________________________________________________________________________________________________________");
  end
  else if(mode == 0 && instruction_string == "HALT") begin
  $display("SIMULATION COMPLETE");
  $display("Total Instructions Executed: %0d", num_instructions);
  #100;
  $stop;
  end
end

endmodule
