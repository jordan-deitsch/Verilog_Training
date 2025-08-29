// top level module for rtl alu
module top();

  // generate the clock
  bit clk = 0;
  initial
   forever #50 clk = !clk;

    // alu_if instance
  alu_bfm_if a_bfm_if(.clk(clk));

    // DUT instance
  alu_rtl alu (
    .val1(a_bfm_if.val1),
    .val2(a_bfm_if.val2),
    .mode(a_bfm_if.mode),
    .clk(a_bfm_if.clk),
    .valid_i(a_bfm_if.valid_i),
    .valid_o(a_bfm_if.valid_o),
    .result(a_bfm_if.result)
    );

 initial
   alu_pkg::v_alu_bfm_if = a_bfm_if;

endmodule
