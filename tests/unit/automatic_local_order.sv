module automatic_local_order(
	input logic sel,
	input logic [5:0] seed
);
	logic [5:0] actual;
	logic [5:0] expected;

	function automatic logic [5:0] recurse(input logic [1:0] n, input logic [5:0] value);
		automatic logic [5:0] tmp;
		automatic logic [5:0] child;
		begin
			tmp = value ^ {4'b0000, n};
			if (n != 0) begin
				if (sel) begin
					child = recurse(n - 2'd1, tmp + 6'd3);
					tmp = tmp ^ {child[2:0], child[5:3]};
				end else begin
					child = recurse(n - 2'd1, tmp + 6'd5);
					tmp = tmp + {child[0], child[5:1]};
				end
			end
			recurse = tmp;
		end
	endfunction

	always_comb begin
		logic [5:0] f2_tmp;
		logic [5:0] f2_child;
		logic [5:0] f1_input;
		logic [5:0] f1_tmp;
		logic [5:0] f1_child;

		actual = recurse(2'd2, seed);

		f2_tmp = seed ^ 6'd2;
		if (sel) begin
			f1_input = f2_tmp + 6'd3;
			f1_tmp = f1_input ^ 6'd1;
			f1_child = (f1_tmp + 6'd3) ^ 6'd0;
			f2_child = f1_tmp ^ {f1_child[2:0], f1_child[5:3]};
			expected = f2_tmp ^ {f2_child[2:0], f2_child[5:3]};
		end else begin
			f1_input = f2_tmp + 6'd5;
			f1_tmp = f1_input ^ 6'd1;
			f1_child = (f1_tmp + 6'd5) ^ 6'd0;
			f2_child = f1_tmp + {f1_child[0], f1_child[5:1]};
			expected = f2_tmp + {f2_child[0], f2_child[5:1]};
		end

		if (sel !== 1'bx)
			assert(actual === expected);
	end
endmodule
