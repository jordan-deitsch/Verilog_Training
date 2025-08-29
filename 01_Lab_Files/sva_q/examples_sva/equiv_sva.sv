module equiv_sva;

reg a,b,c,clk;

initial begin clk = 0; forever #20 clk = !clk; end

initial begin
 a = 0;
 b = 0;
 c = 0;
 @(negedge clk);
 a = 1;
 @(negedge clk);
 a = 0;
 repeat (3)@(negedge clk);
 a = 0; b = 1;
 @(negedge clk);
 b = 0;
 @(negedge clk);
 b = 1;
 repeat (2)@(negedge clk);
 c = 1;
 #200 $stop;
 $assertoff(100,ap3a);
 a = 0;
 b = 0;
 c = 0;
 @(negedge clk);
 a = 1;
 @(negedge clk);
 a = 0;
 repeat (3)@(negedge clk);
 a = 0; b = 1;
 @(negedge clk);
 b = 0;
 @(negedge clk);
 b = 1;
 repeat (2)@(negedge clk);
 c = 1;
 #200 $stop;
 
end

property p1a;
  @(posedge clk) (a == 1) |-> a ##[1:$] b  ;
endproperty
ap1a: assert property (p1a); 

property p1b;
  @(posedge clk) (a == 1) |-> a ##1 b[->1]  ;
endproperty
ap1b: assert property(p1b); 

ap3a: assert property (@(posedge clk) (a == 1) |-> a ##1 b[->3] ##1 c);
ap3b: assert property (@(posedge clk) (a == 1) |-> a ##1 ((!b[*0:$] ##1 b)[*3]) ##1 c);



endmodule
