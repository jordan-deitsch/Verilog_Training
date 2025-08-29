interface my_if();
 bit clk = 0;
 bit [2:0] b = 0;
 always #20 clk = !clk;
 always @(negedge clk)
  b++;
endinterface
