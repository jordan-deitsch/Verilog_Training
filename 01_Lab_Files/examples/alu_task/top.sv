// top level module for rtl alu
module top();


  // generate the clock
  bit clk = 0;
  initial
   forever #50 clk = !clk;

    // alu_if instance
  alu_bfm_if alu_bfm_if(.clk(clk));

    // DUT instance
  alu_rtl alu (
    .val1(alu_bfm_if.val1),
    .val2(alu_bfm_if.val2),
    .mode(alu_bfm_if.mode),
    .clk(alu_bfm_if.clk),
    .valid_i(alu_bfm_if.valid_i),
    .valid_o(alu_bfm_if.valid_o),
    .result(alu_bfm_if.result)
    );
    

endmodule
