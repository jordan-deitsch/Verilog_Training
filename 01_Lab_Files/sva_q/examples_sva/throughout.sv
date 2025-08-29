module t_throughout;
bit clk, burst, trdy, start;


initial
  begin
    clk = 0;
    forever #20 clk = !clk;
  end
    
initial
  begin
    start = 0;
    burst = 1;
    trdy = 1;
    @(posedge clk)
      start = 1;
      burst = 0;
    repeat (2) @(posedge clk);
      trdy = 0;
    repeat(2) @(posedge clk);
      burst = 1; 
    @(posedge clk);
      trdy = 1;
    repeat(3) @(posedge clk);
    $stop;    
  end


sequence burst_rule;
   @(posedge clk)
          $fell (burst) ##0
	    (!burst) throughout (##2 (!trdy [*3]));
endsequence

property p_burst_rule;
   @(posedge clk)
   $rose(start) |-> burst_rule;
endproperty

assert property (p_burst_rule)
    else $display ("Burst Rule Failed");

endmodule
