module uncond_extend;
bit a = 0;
bit b = 0;
bit c = 0;
bit clk = 0;


always #20 clk = !clk;


initial begin

  @ (negedge clk) a = 1;
  @ (negedge clk) a = 0;
     b = 1;
  @ (negedge clk) b = 0;
  repeat (3) @ (negedge clk); 
//
  @ (negedge clk) $stop;
end

sequence s_uncond_extend;
  @(posedge clk)  a ##1 b ##2 1;// sequence extended by clock 2 ticks
endsequence
property p_uncond_extend;
  @(posedge clk) a |-> a ##1 b ##2 1;	 
endproperty

a_uncond_extend:  assert property(p_uncond_extend);

always @ (s_uncond_extend)
  $display("%0d p_uncond_extend matched",$time); 


endmodule
