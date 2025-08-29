`define true 1
module goto_repetition;
bit a = 0;
bit b = 0;
bit c = 0;
bit clk = 0;


always #20 clk = !clk;


initial begin
  @ (negedge clk)
    a = 1;
  @ (negedge clk)
    a = 0;
  @ (negedge clk)
    b = 1;
  @ (negedge clk)
    b = 0;
    c = 1;
  @ (negedge clk)
    b = 1;
    c = 0;
  @ (negedge clk)
//    b = 0;
  @ (negedge clk)
    b = 1;
//  @ (negedge clk);
//  @ (negedge clk)
    c = 1;
  @ (negedge clk)
//    c = 1;
//    b = 1;

  @ (negedge clk) #100 $stop;
end


property p_goto_repetition;
  @(posedge clk) a |-> a ##1 b [->2] ##2 c  ;
endproperty

a_goto_repetition:   assert property(p_goto_repetition);


endmodule
