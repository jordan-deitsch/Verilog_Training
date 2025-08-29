/*******************************
*  Sample solution:   - Synthesizable  RTL
*  - Separate signals, One-hot encoding
*  - Requires "beh_sram.v" ( SRAM model)
*  - this is the seqential part
*/

module sm_seq ( into, outof, rst, clk, mem, addr, rd_, wr_);

input [31:0] into;
output [31:0] outof;
input rst, clk;
inout [31:0] mem;
output [9:0] addr;
output rd_, wr_;

parameter DLY = 1;

reg [31:0] in_reg, outof,
	 w_data, r_data;
reg [9:0] addr;
reg wr_;

tri [31:0]  mem = wr_ ? 32'bZ : w_data;

// instantiate the state machine module
sm sm_0(
    .clk     (clk),
    .rst     (rst),
    .opcode  (in_reg[31:28]),
    .a_wen_n (a_wen_n),
    .wd_wen_n(wd_wen_n),
    .rd_wen_n(rd_wen_n),
    .inca    (inca)
  );

wire rd_ = rd_wen_n;

always @ (posedge clk)
  if (rst)
    begin
	    in_reg <= into; // get the input
      outof  <= r_data; // send the output
	    addr   <= in_reg[9:0];
	    w_data <= in_reg;
	    wr_    <= 1'b1;
 	    r_data <= mem;
    end
  else begin
	  in_reg <= into; // get the input
    outof  <= r_data; // send the output
	  if (!a_wen_n)
	    addr <= in_reg[9:0];
	  else if (inca)
	    addr <= addr + 1;
	  if (!wd_wen_n)
	    w_data <= in_reg;
	  wr_ <= wd_wen_n;
	  if (!rd_wen_n)
 	    r_data <= mem;
  end
endmodule

