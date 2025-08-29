module with_in;
bit clk = 0;
bit a = 0;
bit b = 0;
bit c = 0;
bit start = 0;

always #20 clk = !clk;
    
initial
  begin
    @(negedge clk)
      start = 1;
      b = 1;
    @(negedge clk);
      a = 1;
    repeat(5) @(negedge clk);
      a = 0;
    @(negedge clk);
      b = 0;
    $stop;    
  end

sequence s_within;
  a[*5] within ( $rose ( b) ##1 b[*6] );
endsequence

property p_within;
   @(posedge clk)
   $rose(start) |-> s_within;
endproperty

assert property (p_within);

endmodule
