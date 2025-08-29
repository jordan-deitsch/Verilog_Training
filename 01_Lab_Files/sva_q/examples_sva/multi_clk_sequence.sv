module multi_clk_sequence;

bit clk0 = 0;
bit clk1 = 0;
bit a,b;

always #20 clk0 = !clk0;
always #30 clk1 = !clk1;

initial begin
 @ (posedge clk0);
  a = 1;
 @ (posedge clk0);
  a = 0;
end 


initial begin
 @ (posedge clk1);
  b = 1;
 @ (posedge clk1);
  b = 0;
  
  #200 $stop;
end 

sequence m_clk_ex;
   @(posedge clk0)  a  ##1  @(posedge clk1) b;
endsequence

property p_clk_ex;
  m_clk_ex;
endproperty

a_clk_ex:  assert property(p_clk_ex) $display ("passed");
  else $display("failed");
  
endmodule
