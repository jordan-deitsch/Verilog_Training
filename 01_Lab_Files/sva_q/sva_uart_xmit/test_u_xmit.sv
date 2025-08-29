/////////////////////////////////////////////////
//
//  Testbench for WHDL sv_assertions Labs
//
// Uses an RTL UART made available by Jeung Joon Lee
// from his free-IP website: www.cmosexod.com
//
//

module test_u_xmit;
reg sys_clk, sys_rst_l, xmit;
reg [7:0] data;
reg [3:0] sys_clk_div16;
wire done, uart_out;
wire uart_clk = sys_clk_div16[3];
integer i;
bit bad = `BAD;

// create sys_clk
initial begin
  sys_clk = 0;
  forever #30 sys_clk = !sys_clk;
end

// create 16x slower clock (uart_clk)
always @(posedge sys_clk)
 if(bad && !sys_rst_l)
     sys_clk_div16 = sys_clk_div16 +2;
 else
  sys_clk_div16 = sys_clk_div16 +1;

// main test
initial begin
  // init signals
  sys_rst_l = 1;
  sys_clk_div16 = 0;
  xmit = 0;
  data = 0;
  // wait 5 clocks
  repeat(5)@(posedge uart_clk);
  if(bad)

    $display("\n",$stime(),,"*****Forcing uart_clk to not be sys_clk/16 - should see an assertion error");
  sys_rst_l = 0; // assert reset
  // wait 2 clocks
  repeat(2)@(posedge uart_clk);
  sys_rst_l = 1; // deassert reset
  repeat(10)@(posedge uart_clk); // wait 10 clocks
  // transmit stimulus
  $display("");
  for(i = 10; i < 21; i = i+1)
    transmit(i);
  if(bad == 1) begin
    repeat(2)@(posedge uart_clk);
    data_change_xmit('hcc);
    repeat(5)@(posedge uart_clk);
    xmit_short('hbb);
  end
  repeat(2)@(posedge uart_clk); // wait 2 clocks
  $display("");
  $finish();  // done
end

// task for transmitting data
task transmit(input bit[7:0] d_in);
  bit[7:0] d_out;
  wait(done);
  @(posedge uart_clk) #1;
  data <= #1 d_in;
  xmit <= #1 1;
  @(posedge uart_clk);
  // clear data and xmit
  data <= #1 0;
  xmit <= #1 0;
  // gather output
  for (int i = 0; i <8; i++)
    @ (posedge uart_clk)
      d_out[i] <= uart_out;
  wait(done);
  // check what was sent
  if(d_in == d_out)
    $display($stime(),,"Success! Data transmitted: %h",d_out);
  else
    $display($stime(),, "Failure!! Data transmitted: %h, should have been %h",d_out, d_in);
endtask

// task for transmitting data with data changing during xmit
task data_change_xmit(input bit[7:0] d_in);
  bit[7:0] d_out;
  wait(done);
  @(posedge uart_clk);
  // set data and xmit
  data <= #1 d_in;
  xmit <= #1 1;
  @(negedge uart_clk);
  // clear data too soon
  $display("\n",$stime(),,"*****Changing data too soon - should see an assertion error",);
  data <= #1 0;
  @(posedge uart_clk);
  xmit <= #1 0;
  wait(done);
endtask

// task for transmitting data with bad xmit signal (too short)
task xmit_short(input bit[7:0] d_in);
  bit[7:0] d_out;
  wait(done);
  @(posedge uart_clk);
  // set data and xmit
  data <= #1 d_in;
  xmit <= #1 1;
  @(negedge uart_clk);
  // clear xmit too soon
  $display("\n",$stime(),,"*****Clearing xmit too soon - should see an assertion error",);
  xmit <= #1 0;
  @(posedge uart_clk);
  data <= #1 0;
  wait(done);
endtask


u_xmit U1( .* );




// simple post-reset checkers


sequence s_uart_sys16;
  uart_clk[*8] ##1 !uart_clk[*8] ##1 uart_clk;
// Alternative:  Non duty-cycle dependant but less efficient
//  ##1(!$rose(uart_clk)) [*15] ##1 $rose(uart_clk);
endsequence

sequence s_xmit_hi16;
  @(posedge sys_clk) xmit[*16]##1 !xmit;
endsequence

sequence s_xmit_done;
//  ##1 !done && !uart_out;
  ##1 $fell(done) && $fell(uart_out);
endsequence

sequence s_xmit_nc_data;
   $stable(data) [*1:$] ##1 !xmit;
endsequence

sequence s_rst_sigs;
   ##1 (uart_out && !done);
//   ##1 $rose(uart_out) && $fell(done);
endsequence

sequence s_rst_done;
//  (!sys_rst_l) [*1:$] ##1 sys_rst_l ##1 (done && !xmit) [*1:$] ##1 xmit ;
  (sys_rst_l)[->1] ##1 !xmit ##0 $rose(done) ##0 (done throughout ((xmit)[->1]));
endsequence

sequence s_rst_pair;
  s_rst_done and s_rst_sigs;
endsequence

property p_rst_sigs;
  @(posedge sys_clk) ($fell(sys_rst_l)) |-> s_rst_sigs;
endproperty

property p_rst_done;
  @(posedge sys_clk) ($fell(sys_rst_l)) |-> s_rst_done;
endproperty

property p_post_rst;
  @(posedge sys_clk) ($fell(sys_rst_l)) |-> s_rst_pair;
endproperty

//####################
// sys_clk checkers
//####################
//
// sys_clk divider checker

property p_uart_sys16;
  @(posedge sys_clk) $rose(uart_clk) && !sys_rst_l  |-> s_uart_sys16;
endproperty

//
// xmit and data checks

property p_xmit_hi16;
  @(posedge sys_clk) $rose(xmit) |-> s_xmit_hi16;
endproperty

property p_xmit_done;
  @(posedge sys_clk) $rose(xmit) |-> s_xmit_done;
endproperty


//
// Serial protocol checkers

property p_xmit_nc_data;
  @(posedge sys_clk) ($rose(xmit)) |=> s_xmit_nc_data;
endproperty


// LAB  Write your serial bitstream checker here



// assertions

assert_uart_sys16: assert property (p_uart_sys16) //$display("%m :OK!");
                       else $display("%m : uart_clk should = sys_clk/16");

assert_rst_sigs: assert property (p_rst_sigs) //$display("%m :OK!");
                       else $display("%m : Signals uart_out and done failed to reset");

assert_rst_done: assert property (p_rst_done) //$display("%m :OK!");
                       else $display("%m : Problems with done after reset");

assert_post_rst: assert property (p_post_rst) //$display("%m :OK!");
                       else $display("%m : device did not reset");

assert_xmit_hi16: assert property (p_xmit_hi16) //$display("%m :OK!");
                       else $display("%m : Signal xmit should stay hi for 16 sys_clks");

assert_xmit_done: assert property (p_xmit_done) //$display("%m :OK!");
                       else $display("%m : Posedge xmit should take done and uart_out low.");

assert_xmit_nc_data: assert property (p_xmit_nc_data) //$display("%m :OK!");
                       else $display("%m : data should not change while xmit asserted");




//####################
// uart_clk checkers
//####################
//
//


property p_xmit_hi1;
  @(posedge uart_clk) $rose(xmit) |-> ##1 $fell(xmit);
endproperty

property p_done_11;
  @(posedge uart_clk) ($fell(done) && xmit ) |=> /* s_xmit_hi16.matched */ ##10 $rose(done);
endproperty


assert_xmit_hi1: assert property (p_xmit_hi1) //$display("%m :OK!");
                       else $display("%m : Signal xmit should stay hi for 1 uart_clk");

assert_done_11: assert property (p_done_11) //$display("%m :OK!");
                       else $display("%m : Byte transmission (done low) should take 11 uart_clks");


endmodule

