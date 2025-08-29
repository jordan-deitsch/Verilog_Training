module beh_sram(ip,op,clk,rw_);
input packet ip;
output packet op;
input bit clk, rw_;

packet ret_pkt;
bit doit;
reg [31:0] mem [0:1023];


always @(posedge clk)
  if(rw_ ) // read
    begin
      ret_pkt.data = mem[ip.addr];
      ret_pkt.addr = ip.addr;
      op <= #5 ret_pkt;
    end
  else		// write
    begin
      mem[ip.addr] <= ip.data;
    end

endmodule

