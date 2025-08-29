module top;
import types::*;

dut_if d_if();  // interface intstance
   //ap interface to dut
dut DUT(.data_rcvd(d_if.data_rcvd), .clk(d_if.clk));
  // sink object with interface argument
sink       snk = new(d_if);
source    src = new(2);  // source object
mailbox #(Packet)  src2snk = new(1); //mailbox

initial
  begin
       src.out_chan = src2snk;    // via mailboxes
       snk.in_chan  = src2snk;
       fork
          src.run(); // start generators
          snk.run(); // start sinks
       join_none
       #0;
  end

  initial #200 $finish();
endmodule
