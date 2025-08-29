module dut(input int data_rcvd, input bit clk);

always @(posedge clk)
begin
  $display("%m received data:  %0d",
  data_rcvd);
end
endmodule
