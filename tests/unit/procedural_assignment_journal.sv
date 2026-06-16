module procedural_assignment_journal(
	input logic sel,
	input logic [7:0] seed
);
	logic [7:0] actual;
	logic [7:0] expected;

	always_comb begin
		actual = seed;
		expected = seed;

		if (sel) begin
			{actual[0], actual[7], actual[3:2]} = {seed[6], seed[1], seed[5:4]};
			expected[0] = seed[6];
			expected[7] = seed[1];
			expected[3:2] = seed[5:4];
		end else begin
			{actual[6:5], actual[1]} = {seed[2:1], seed[7]};
			expected[6:5] = seed[2:1];
			expected[1] = seed[7];
		end

		if (sel !== 1'bx)
			assert(actual === expected);
	end
endmodule
