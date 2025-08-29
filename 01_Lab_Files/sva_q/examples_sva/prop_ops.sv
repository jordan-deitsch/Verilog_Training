module prop_ops;
bit a = 0;
bit b = 0;
bit c = 0;
bit t1 = 0;
bit t2 = 0;
bit t3 = 0;
bit clk = 0;


always #20 clk = !clk;


initial begin
  $vcdpluson;
// or
  @ (negedge clk)
   t1 = 1;
   b = 1;
  @ (negedge clk)
   t1 = 0;
   b = 0;
   c = 1;
  @ (negedge clk) c = 0;
// and
  @ (negedge clk)
   t2 = 1;
   a = 1;
   b = 1;
   c = 1;
  @ (negedge clk)
   t2 = 0;
  @ (negedge clk)
   a = 0;
   b = 0;
   c = 0;
// and try offset
  @ (negedge clk)
   a = 1;
  @ (negedge clk);
   a = 0;
   b = 1;
  @ (negedge clk)
   b = 0;
   c = 1;
  repeat(4) @(negedge clk);
  $finish;
end 

sequence s1;
  a ##1 b;
endsequence

sequence s2;
  b ##1 c ##1 !c;
endsequence

property p_or;
  @ (posedge clk) t1 |-> s1 or s2 ;
endproperty

property p_and;
  @ (posedge clk) t2|-> s1 and s2 ;
endproperty

property p_int;
  @ (posedge clk) t2|-> s1 intersect s2 ;
endproperty

// won't compile
property p_if;
  @ (posedge clk) t2|-> if(c) s1 else s2 ;
endproperty


a_p_or:   assert property(p_or);
a_p_and:  assert property(p_and);
a_p_int:  assert property(p_int);
a_p_if:  assert property(p_if);

endmodule
