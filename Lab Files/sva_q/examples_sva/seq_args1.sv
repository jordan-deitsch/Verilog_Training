
module formal_args;

logic [7:0] a = 0;
logic [7:0] data_bus = 0;
logic [0:3] c_be;
logic [0:3] b;
bit clk = 0;
bit frame = 0;
bit c = 0;
bit start_sig = 0;
bit end_sig = 0;

always #20 clk = !clk;

sequence s1;
   @ (posedge clk)
         a ##1 b ##1 c; 		// s1 evaluates on each successive edge of clk
endsequence

sequence s2 (data,en);		// sequence with name AND arguments
   (!frame && (data ==data_bus)) ##1 (c_be[0:3] == en);
endsequence

sequence s3;
   start_sig ##1 s2(a,b)  ##1 end_sig; 	// sequence as sub-expression
endsequence



endmodule
