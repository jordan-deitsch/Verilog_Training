`define true 1
module value_change;
bit st = 0;  
bit a = 0;
bit b = 0;
bit c = 0;
bit d = 0;
bit clk = 0;


always #20 clk = !clk;


initial begin
  $vcdpluson;
// first pattern PASS
  @ (negedge clk)
    st = 1;
    a = 1;
    b = 1;
    c = 0;
  @ (negedge clk)
    st = 0;
    a = 0;
    d = 1;
  @ (negedge clk)
    a = 0;
    b = 0;
    c = 0;
    d = 0;
  @ (negedge clk)

  
// second pattern FAIL [ $stable( b&c) ]
  @ (negedge clk)
    st = 1;
    a = 1;
  @ (negedge clk)
    st = 0;
    a = 0;
    c = 1;
    b = 1;
    d = 1;
  @ (negedge clk)
    a = 0;
    b = 0;
    c = 0;
    d = 0;
  @ (negedge clk)

  
// thrid pattern FAIL [ $fell(d) ]
  @ (negedge clk)
    st = 1;
    a = 1;
  @ (negedge clk)
    st = 0;
    a = 0;
  @ (negedge clk)
    a = 0;
    b = 0;
    c = 0;
    d = 1;

  @ (negedge clk) $finish;
end


//************ [*0:M]

property p_range_rep_0_exa;
  @(posedge clk) $rose(st) |-> $rose(a) ##1 $stable(b&c) ##1 $fell(d);
endproperty


a_funcs:   assert property(p_range_rep_0_exa);


endmodule
