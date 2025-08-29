module my_svas (input clk,
                input [2:0] d);
 property p1;
   @ (posedge clk)
     d==2 |-> ##1 d==3 ##1 d==4;
 endproperty
 a1: assert property(p1) $display ("%m p1 passed");
         else $display("%m p1 failed");
endmodule
