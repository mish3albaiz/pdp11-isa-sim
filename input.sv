// input.sv - ECE586 Final Project - PDP Simulator Testbench
//
// Meshal Albaiz
// Tapasya Bhatnagar
// Tristan Cunderla
// Ruben Maldonado
//
// Winter 2019
// 2/18/2019
//
// DESCRIPTION______________________________________________________________________________
// This is the top module for the PDP-11 simulator.  This module will take initial
// settings from the user as well as populate an array from a trace file containing
// ASCII values that were calculated from the ASCII translator.  This module will
// determine whether or not the starting address will be decided by the user or
// by the tracefile.  This module will also determine what display mode the simulator
// will be in.
//__________________________________________________________________________________________

module sim_in;

//____________________________
// Parameters and Variables
//____________________________

logic clk; // clock
string str; // file name
reg [8*7:1] line;
reg [7:0] sign;
reg [8*6:1] number;
integer file, outfile;
logic [7:0] sign_bit;
reg [8*7:1] trans;
parameter N = 64000;
logic [27:0] data [N-1:0]; // array of data in trace file
logic [19:0] address [N-1:0]; // array of data concatenated into instruction and address
logic [27:0] data_temp;
integer i,j,k;
logic [19:0] input_in;
logic [17:0] data_out;
bit dm;
logic [17:0] addr;
logic signed [8:0] offset;
logic signed [7:0] offset_temp;
logic signed [31:0] count;

logic [15:0] reg0, reg1, reg2, reg3, reg4, reg5, reg6;
logic signed [15:0] reg7;
logic [3:0] NZVC;
string instruction_string, regd_string, regs_string;
logic [1:0] instruction_type;
logic [63:0] instruction_num;
logic B_Flag, J_Flag;
logic [19:0] temp;
integer PC_temp;
logic [15:0] PC;

//____________________________
// Clock
//____________________________

initial clk = 1'b0; // clock initially on
always #5 clk = ~clk; // flip with 5 delay

//____________________________
// instantiation
//____________________________

sim_output sim_output(.data_in(data_out));

//________________________________________________
// Getting User Input Function and Filling Array
//________________________________________________


PDP11 PDP11(.input_in(input_in), .output_out(data_out), .reg0(reg0), .reg1(reg1), .reg2(reg2), .reg3(reg3), .reg4(reg4), .reg5(reg5), .reg6(reg6), .reg7(reg7), .NZVC(NZVC), .instruction_string(instruction_string), .regd_string(regd_string), .instruction_type(instruction_type), .instruction_num(instruction_num), .regs_string(regs_string), .B_flag(B_Flag), .offset_temp(offset), .J_flag(J_Flag), .PC_temp(PC), .count(count));
display display(.mode(dm), .instruction_string(instruction_string), .registers_val({reg7, reg6, reg5, reg4, reg3, reg2, reg1, reg0}), .registerD(regd_string), .registerS(regs_string), .flags(NZVC), .instruction_type(instruction_type), .num_instructions(instruction_num));

initial begin

// getting file name
$value$plusargs("File=%0s", str);
// getting display mode from user
$value$plusargs("DispMode=%b", dm);

// assigning file names, and determine file options
file = $fopen(str, "r");
outfile = $fopen("out1.txt","w");

// until the end of the file do this...
while (! $feof(file)) begin
	// getting each line and making it a string
	$fscanf(file,"%0s",line);
	// differentiating between the first symbol and the rest of the line
	sign = line[8*7:8*6+1];
	number = line[8*6:1];
	// if first symbol is a *
	if (sign == 8'h2a) begin
		sign_bit = "2";
	end
	// if first symbol is a @
	else if (sign == 8'h40) begin
		sign_bit = "1";
	end
	// if first symbol is a -
	else begin
		sign_bit = "0";
	end
	// concatenating translated info
	trans = {sign_bit,number};
	// writing new info to file out1.txt
	$fdisplay(outfile,"%0s", trans);
	#10;
end
// closing both files
$fclose (file);
$fclose (outfile);
#100;
// reading the output file that was just created
$readmemh("out1.txt", data);
#100;

// filling address array with octal values with hex values from data
j = 0;
i = 0;
for(i = 0 ; i < N ; i = i + 1) begin
		data_temp = data[i];
		address[j] = {data_temp[25:24],data_temp[22:20],data_temp[18:16],data_temp[14:12],data_temp[10:8],data_temp[6:4],data_temp[2:0]};
		j = j+1;
end
count = 32'b0;
B_Flag = 1'b0;
J_Flag = 1'b0;
end

always @ ( posedge clk ) begin
		#1000000
		if (address[count] !== 20'bx && B_Flag == 1'b1) begin
			offset_temp = offset >> 1;
			input_in = address[count + offset_temp];
			count = count + offset_temp + 1;
		end
		else if (address[count] !== 20'bx && J_Flag == 1'b1) begin
			PC_temp = PC >> 1;
			input_in = address[PC_temp];
			count = PC_temp + 1;
		end
		else if (address[count] !== 20'bx && B_Flag == 1'b0) begin
			input_in = address[count];
			count = count + 1;
		end
		else if (address[count] == 20'bx) begin
			$stop;
		end
end

endmodule
