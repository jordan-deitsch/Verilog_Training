
module ended;

reg clk, ready, reset, branch_back, proc1, proc2, inst;

initial begin
 clk = 0;
 ready = 0;
 reset = 0;
 branch_back = 0;
 proc1 = 0;
 proc2 = 0;
 inst = 0;
 forever #50 clk = !clk;
end

initial begin
  @ (negedge clk)
    ready = 1;
    reset = 1;
  @ (negedge clk)
    ready = 0;
    proc1 = 1;
    reset = 0;
    inst = 1;
  @ (negedge clk)
    proc1 = 0;
    proc2 = 1;
    inst = 0;
  @ (negedge clk)
    proc2 = 0;
    branch_back = 1;
  @ (negedge clk)
    branch_back = 0;
  repeat (3)   @ (negedge clk);
  $stop();
  
end

sequence e1;
   @(posedge clk) ##1 proc1 ##1 proc2;
endsequence

sequence rule;
  ##1 inst ##1 e1.ended ##1 branch_back;
endsequence

property p_e1;
  @(posedge clk) $rose(ready) |-> e1;
endproperty

property p_rule;
  @(posedge clk) $rose(reset) |-> rule;
endproperty

//assert_e1:  assert property(p_e1)
//                  else $display("e1 failed");

assert_rule:  assert property(p_rule)
                  else $display("rule failed");
                

endmodule
