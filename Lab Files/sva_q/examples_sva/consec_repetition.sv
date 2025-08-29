`define true 1
module consec_repetition;
bit a = 0;
bit b = 0;
bit c = 0;
bit d = 0;
bit clk = 0;


always #20 clk = !clk;


initial begin
// range_rep_0_exa & b
  @ (negedge clk)
    a = 1;
    d = 1;
  @ (negedge clk)
    a = 0;
    d = 0;
  @ (negedge clk)
    b = 1;
  @ (negedge clk)
    b = 0;
//    c = 1;
  @ (negedge clk)
    c = 0;
    a = 1;
  @ (negedge clk)
    a = 0;
  @ (negedge clk)
    b = 1;
  @ (negedge clk)
    b = 0;
    c = 1;
  @ (negedge clk)
    c = 0;

  @ (negedge clk) $stop;
end


property p_consec_repetition;
  @(posedge clk) d |-> (a ##2 b) [*1:2] ##1 c;
endproperty

a_consec_repetition:   assert property(p_consec_repetition);


endmodule
