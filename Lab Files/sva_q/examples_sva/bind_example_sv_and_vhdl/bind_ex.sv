module bind_ex; 
 my_if my_if_inst();
 my_design m1(.clk(my_if_inst.clk),
              .b(my_if_inst.b) );
 my_design m2(.clk(my_if_inst.clk),
              .b(my_if_inst.b) );
 bind my_design my_svas MS(.clk, .d);
endmodule
