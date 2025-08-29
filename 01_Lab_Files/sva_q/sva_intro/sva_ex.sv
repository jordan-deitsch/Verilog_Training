module sva_ex;


logic [2:0] cnt;
logic clk;

initial
  begin
    clk = 0;
    cnt = 0;
    forever #20 clk = !clk;
  end

initial
  begin
    wait(cnt == 2) cnt = 4;
    #240 $stop;
  end  
    
always @(posedge clk)
  cnt <= #1 cnt +1;


sequence s_count3;
   (cnt == 3'h1) ##1 (cnt == 3'h2) ##1 (cnt == 3'h3); 
endsequence

property p_count3;
  @(posedge clk) (cnt == 3'h0) |=> s_count3;
endproperty

assert_count3: assert property (p_count3);


endmodule
