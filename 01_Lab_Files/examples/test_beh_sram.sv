module tb;
bit clk, rw_;
packet in_pkt, out_pkt;

initial
  begin
    clk = 0;
    forever #20 clk = !clk;
  end
  
beh_sram U1(.ip(in_pkt), .op(out_pkt), .clk(clk), .rw_(rw_));

task wr_pkt(input logic [9:0] addr,
		         input logic[31:0] data);
begin
  @(negedge clk);
  rw_ = 0;
  $display($stime,,"Writing %h to address %h",data, addr);
  in_pkt = {addr,data};
  @(posedge clk);
end
endtask		  

task rd_pkt(input logic [9:0] addr,
		input  logic[31:0] data);
begin
@(negedge clk);		  
in_pkt = {addr, 0};
rw_ = 1;
@(posedge clk) #6; 
if(out_pkt.data === data)
  $display ($stime," Read successful: %h from address %h", out_pkt.data, addr);
else  
  $display ($stime," Read failed: %h, expected: %h", out_pkt.data, data);
end 
endtask		  

initial
begin
  $display("\n\n\n");
  #10;
  wr_pkt(5,10);
  #10;
  wr_pkt(1,2);
  #10;
  rd_pkt(5,10);
  #10;
  rd_pkt(1,2);
  #10;
  wr_pkt('h1ff,'haaaa);
  #10;
  rd_pkt('h1ff,'haaaa);
  #10;
  $display("\n\n\n");
  $stop;
end  

endmodule




/*
        40 Writing 0000000a to address 005
        80 Writing 00000002 to address 001
       146 Read successful: 0000000a from address 005
       186 Read successful: 00000002 from address 001
       200 Writing 0000aaaa to address 1ff
       266 Read successful: 0000aaaa from address 1ff
*/
