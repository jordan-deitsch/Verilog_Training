module my_design (input bit clk, input bit [2:0] b);
 bit[2:0] d;
 always @ (posedge clk)
   d <= b;
endmodule
