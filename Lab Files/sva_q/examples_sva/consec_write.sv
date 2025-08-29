module consec_write;
logic [7:0] addr;
logic [15:0] dat;
logic wr_en;
bit clk;

always #20 clk = !clk;

initial begin

addr = 0;
dat = 0;
wr_en = 0;
clk = 0;

// write 2 different addresses consecutively
repeat(2) @(negedge clk);
addr = 10;
dat = 100;
wr_en = 1;
@(negedge clk);
wr_en = 0;
addr = 11;
@(negedge clk);
addr = 12;
dat = 200;
wr_en = 1;
@(negedge clk);
wr_en = 0;
addr = 13;


// write same address twice consecutively

repeat(2) @(negedge clk);
addr = 10;
dat = 111;
wr_en = 1;
@(negedge clk);
wr_en = 0;
addr = 11;
@(negedge clk);
addr = 10;
dat = 222;
wr_en = 1;
@(negedge clk);
wr_en = 0;
addr = 11;

end

sequence s1(prev);
	(1'b1, prev = addr) ##1 wr_en[->1] ;
endsequence

property p_no_consec_writes;
logic[7:0] prev_addr;


//@(posedge clk) wr_en |-> wr_en[->1] ##0 if(did_write) (addr !== prev_addr, prev_addr = addr) else ( (addr == addr, prev_addr = addr), did_write = 1 );

//@(posedge clk) wr_en |-> (wr_en == 1, prev_addr = addr) ##0 !wr_en[->1] |=> wr_en[->1] ##0  addr !== prev_addr;

//@(posedge clk) wr_en |-> (1'b1, prev_addr = addr) ##1 wr_en[->1] ##0  addr !== prev_addr;
@(posedge clk) wr_en |-> s1(prev_addr) ##0  addr !== prev_addr;

endproperty	

assert property(p_no_consec_writes);

endmodule