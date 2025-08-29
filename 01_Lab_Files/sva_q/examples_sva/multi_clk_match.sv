module multi_clk_match;
bit a = 0;
bit b = 0;
bit c = 0;
bit d = 0;
bit t1 = 0;
bit t2 = 0;
bit t3 = 0;
bit clk = 0;
bit clk2 = 0;


always #20 clk = !clk;
always #25 clk2 = !clk2;


initial begin
//  $vcdpluson;
// s2
  repeat(1) @ (negedge clk);
  @ (negedge clk)
   t1 = 1;
   c = 1;
  @ (negedge clk)
   t1 = 0;
   c = 0;
  @ (negedge clk)
   d = 1;
  @ (negedge clk)
   d = 0;
  repeat(4) @(negedge clk);
  $finish;
end 
initial begin
// s1
  @ (negedge clk2)
   t2 = 1;
   a = 1;
  @ (negedge clk2)
   t2 = 0;
   a = 0;
   b = 1;
  @ (negedge clk2)
   b = 0;
end
   
   
 

sequence s1;
  @(posedge clk2) a ##1 b;
endsequence

sequence s2;
  @(posedge clk)  c ##1 s1.matched [->1] ##1 d;
endsequence

property p_match;
  @ (posedge clk) t1 |-> s2;
endproperty

property p_s1;
  @(posedge clk2) t2 |-> s1;
endproperty

a_p_match: assert property(p_match);
a_p_s1:    assert property(p_s1);  

endmodule
