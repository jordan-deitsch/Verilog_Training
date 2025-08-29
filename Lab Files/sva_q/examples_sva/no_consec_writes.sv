module local_vars;
logic wr_en;
logic[7:0] addr;
bit clk;

always begin
 #10 clk = !clk;
end

initial
  begin
  	wr_en = 0;
  	addr = 0;
  	clk = 1;
  	#30;			// First time we obey the rules (no consec writes to same address)
  	wr_en = 1;
  	addr = 'h0a;
  	#20;
  	wr_en = 0;
  	addr = 'h0b;
  	#20;
  	wr_en = 1;
  	addr = 'h0c;
   	#20;
  	wr_en = 0;
  	addr = 'h0d;
  	#40;			// now repeat but break the rule :-)
  	wr_en = 1;
  	addr = 'h0a;
  	#20;
  	wr_en = 0;
  	addr = 'h0b;
  	#20;
  	wr_en = 1;
  	addr = 'h0a;
   	#20;
   	$stop;
  end


property no_consec_writes;
	logic[7:0] prev_addr;

	@(posedge clk)
		wr_en |-> (1, prev_addr = addr) ##1 wr_en[->1] ##0 addr !== prev_addr;
endproperty

assert_no_consec_writes: assert property(no_consec_writes);	



endmodule
