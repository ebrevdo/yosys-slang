module port_order(
	input logic [1:0] sel,
	input logic [7:0] a,
	input logic [7:0] b,
	input logic [7:0] c,
	output logic [7:0] y
);
	assign y = sel == 2'b00 ? a : sel == 2'b01 ? b : c;
endmodule
