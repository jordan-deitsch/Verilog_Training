
module top;
import test_params_pkg::ROUTER_SIZE;

// clk generatiion
bit clk;
initial
 forever #50 clk = !clk;

// create interface & DUT
router_bfm #(ROUTER_SIZE) r_bfm (clk);

router_rtl #(ROUTER_SIZE) router(
    .clk(r_bfm.clk),
    .rst(r_bfm.rst),
    .valid(r_bfm.valid),
    .stream_i(r_bfm.stream_i),
    .stream_o(r_bfm.stream_o),
    .busy(r_bfm.busy),
    .valid_o(r_bfm.valid_o)
    ) ;

initial
    test_params_pkg::v_r_bfm =  r_bfm;  // set virtual if
  
endmodule
