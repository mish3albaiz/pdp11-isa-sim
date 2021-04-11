// output.sv - ECE586 Final Project - PDP Simulator Testbench
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
// This module will print out the results from the PDP-11 simulator onto a text file
//__________________________________________________________________________________________

module sim_output(data_in);

// variables
input [17:0] data_in;
logic [17:0] data_out;
integer file_out;

initial begin
  // open output file in write mode
  file_out = $fopen("output.txt","w");
end

// whenever data_in changes execute
always @ (data_in) begin
  // data_out is equal to data_in
  data_out = data_in;
  // print output to text file in desired format
  $fdisplay(file_out,"%o %o", data_out[17:16], data_out[15:0]);
end

endmodule
