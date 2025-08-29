
/*
Test fixture for functional level state machines

*/

module test_sm();

reg [31:0] into, outof;
reg rst, clk;
wire [31:0] out_wire, dat;
wire [9:0]  addr;
wire rd_, wr_;


logic [31:0] shadow_mem[int unsigned ];

// nop instruction
task nop;
# 5 into = {4'b0000,28'h0}; // op_word
endtask

/* the wt_wd op
task wt_wd;
input [31:0] addr,data;
begin
	#5 into = {4'b0010,28'h0}; // op_word
	@ (posedge clk)
	#5 into = addr;
	@ (posedge clk)
	#5 into = data;
end
endtask
*/
// the wt_wd instruction
task wt_wd (input [31:0] addr,data);
	#5 into = {4'b0001,28'h0}; // op
	@ (posedge clk)
	#5 into = addr;
	@ (posedge clk)
	#5 into = data;
	shadow_mem[addr] = data; // write shadow_mem
	$display("%6d Testbench:  Did a single write:  Address = %h, data = %h", $stime(), addr, data );
endtask


/* the wt_blk op
task wt_blk;
input [31:0] addr,data;
begin
	#5 into = {4'b0011,28'h0}; // op_word
	@ (posedge clk)
	#5 into = addr; // send address
	repeat (4)
	 begin
		@ (posedge clk)
		#5 into = data; // send data
		data = data +1; // change the data word
	 end
end
endtask
*/

// the wt_blk instruction
task wt_blk (input [31:0] addr,data);
	#5 into = {4'b0010,28'h0}; // op
	@ (posedge clk)
	#5 into = addr; // send address
	repeat (4)
	 begin
		@ (posedge clk)
		#5 into = data; // send data
		shadow_mem[addr++] = data++; // write shadow_mem
	 end
	$display("%6d Testbench:  Did a block  write:  Start address = %h, start data = %h",  $stime(), addr-4, data-4 );
endtask


/* the rd_wd op
task rd_wd;
input [31:0] addr;
begin
	#5 into = {4'b0100,28'h0}; // op_word
	@ (posedge clk)
	#5 into = addr;
	@ (posedge clk)
	#5 into = 0;  // nop
end
endtask
 */

// the rd_wd instruction
task rd_wd (input [31:0] addr);
begin
	#5 into = {4'b0011,28'h0}; // op
	@ (posedge clk)
	#5 into = addr;
	@ (posedge clk)
	#5 into = 0;  // empty
	repeat(4) @(posedge clk);
	if(outof == shadow_mem[addr])
		$display("%6d Testbench:  Read passed: Address = %h, data = %h",$stime(), addr, outof);
	else
		$display("%6d Testbench:  Read ERROR:  Address = %h, data = %h, should have been = %h",$stime(),addr, outof, shadow_mem[addr]);
end
endtask

initial
	into = 0;  // set to nop to start off

/* the clock */
initial
 begin
	clk = 0;
	rst = 1;
	forever
		#10 clk = !clk;
 end

always @(negedge clk)
	outof <= out_wire; // put output in register

/* tests */
initial
	begin
                rst = 0;
		#5 rst = 1;
                #20 rst = 0;
//		repeat(10000) begin
	   	  repeat(3) @ (posedge clk); // wait for 3 clocks
		  @ (posedge clk) wt_wd('h100,'haa);
		  @ (posedge clk) wt_wd('h30,'hbb);
		  @ (posedge clk) wt_blk('h40,'ha10);
		  @ (posedge clk) rd_wd('h100);
		  @ (posedge clk) rd_wd('h30);
		  @ (posedge clk) rd_wd('h40);
		  @ (posedge clk) rd_wd('h41);
		  @ (posedge clk) rd_wd('h42);
		  @ (posedge clk) rd_wd('h43);
		  @ (posedge clk) nop;
//		end
		#100 $finish();
	end
sm_seq  sm_seq0( .into, .outof(out_wire),
                  .rst, .clk, .mem(dat),
                  .addr, .rd_, .wr_);

beh_sram sram_0(.clk, .dat, .addr,
                .rd_, .wr_);

bind sm sva_container sva_1 (.*);

endmodule

