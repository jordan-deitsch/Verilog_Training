

module sva_container
 import types_pkg::*;
 (
  input state_values state,
  input logic[3:0] opcode,
  input logic clk
  );

//***********************
// LAB:  Put assertion code here
property p_nop;
	@(posedge clk)
	state=="IDLE" && opcode==NOP |=> state == IDLE;
endproperty

property p_wt_wd;
	@(posedge clk)
	state==IDLE && opcode==WT_WD |=>
	state == WT_WD_1 ##1
	state == WT_WD_2 |=>
	state == IDLE;
endproperty

property p_rd_wd;
	@(posedge clk)
	state==IDLE && opcode==RD_WD |=>
	state == RD_WD_1 ##1
	state == RD_WD_2 ##1
	state == IDLE;
endproperty

property p_wt_blk;
	@(posedge clk)
	state==IDLE && opcode==WT_BLK |=>
	state == WT_BLK_1 ##1
	state == WT_BLK_2 ##1
	state == WT_BLK_3 ##1
	state == WT_BLK_4 ##1
	state == WT_BLK_5 ##1
	state == IDLE;
endproperty

assert_p_nop : assert property (p_nop);
assert_p_wt_wd : assert property (p_wt_wd);
assert_p_rd_wd : assert property (p_rd_wd);
assert_p_wt_blk : assert property (p_wt_blk);

endmodule
