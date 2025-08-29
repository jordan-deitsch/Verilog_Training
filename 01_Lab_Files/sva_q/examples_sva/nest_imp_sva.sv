module nest_imp_sva;

reg a,b,c,d,clk;

initial begin clk = 0; forever #20 clk = !clk; end

initial begin
 a = 0;
 b = 0;
 c = 0;
 d = 0;
 @(negedge clk);
 a = 1; b = 1;
 @(negedge clk);
 a = 0;
 repeat (2)@(negedge clk);
 a = 0; b = 0; c = 1;
 @(negedge clk);
 a = 0; b = 0;
 d = 1;
 repeat(4)@(negedge clk);
 a = 1;  d = 0;
 repeat(3)@(negedge clk);
 c = 1; 
 @(negedge clk);
 a = 0; c = 0; b = 1; d = 1;
 repeat (3)@(negedge clk);
 a = 0; b = 0; d = 0;
 @(negedge clk);
 b = 0;





 @(negedge clk);
 b = 1;
 repeat (2)@(negedge clk);
 c = 1;
 #200 $stop;
end

property np1;
  @(posedge clk) 
  ( a == 1 ) |-> ( b[*2:3] ) |-> (##2 c ##1 d)  ;
endproperty

anp1: assert property (np1); 

property np2;
  @(posedge clk) ( a[*4] ) |-> ( ( ## [2:3] b ) and ( c |=> d ) ); 
endproperty

anp2: assert property (np2); 


endmodule
