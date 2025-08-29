module f_match;
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
      a = 1;
    @(negedge clk);
      a = 0;
    @(negedge clk);
      b = 1;
    repeat(6) @(negedge clk);
    $stop;    
  end

sequence any_match;
    a ##[2:5] b;
endsequence

sequence f_match;
    first_match(a ##[2:5] b);
endsequence

property p_any_match;
   @(posedge clk)
   $rose(start) |-> any_match;
endproperty

property p_f_match;
   @(posedge clk)
   $rose(start) |-> f_match;
endproperty

assert property (p_any_match);
assert property (p_f_match);

endmodule
