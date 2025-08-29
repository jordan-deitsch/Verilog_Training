module multi_clk_ended;
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
  $vcdpluson;
// s2
  repeat(1) @ (negedge clk);
  @ (negedge clk)
   t1 = 1;
   c = 1;
  @ (negedge clk)
   t1 = 0;
   b = 1;
   c = 0;
  @ (negedge clk)
   b = 0;
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
end

sequence s1;
  @(posedge clk2) a ##1 @(posedge clk) b;
endsequence

sequence s2;
  @(posedge clk)  c ##1 s1.ended ##1 d;
endsequence

property p_ended;
  @ (posedge clk) t1 |-> s2;
endproperty

property p_s1;
  @(posedge clk2) t2 |-> s1;
endproperty

a_p_ended: assert property(p_ended);
a_p_s1:    assert property(p_s1);  

endmodule
