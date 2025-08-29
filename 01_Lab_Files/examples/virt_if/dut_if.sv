interface dut_if;

  int data_rcvd;
  bit clk = 1;

  always #25 clk = !clk;
 
endinterface
