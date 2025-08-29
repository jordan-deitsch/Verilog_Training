


//program
module
p1(  input [7:0] cin, dcin,
    output [7:0] cout, dcout, 
     input cclk, dclk );

clocking c @(posedge cclk);
  output cout;
  input cin;
endclocking
 
default clocking dc @(posedge dclk);
  output dcout;
  input dcin;
endclocking
 

logic[7:0] s_cin;


initial
begin
     repeat(3) @(dc);                   // Advance time by 3 posedges of dclk
     s_cin = c.cin;			// Capture cin value sampled on last cclk
     @(dc);
end






//endprogram
endmodule

module top;
logic[7:0] cout,dcout;
bit cclk , dclk;
logic [7:0] cin = 0, dcin = 10;

p1 p1 (.*);

initial
  fork
    forever #10 cclk = !cclk;
    #2 forever #10 dclk = !dclk;
  join

initial forever begin #5 cin = cin +1; dcin = dcin +1; end

//initial $monitor($stime,,"addr: %h, data: %h, cs: %b, rw_: %d, clk: %b",addr,data,cs,rw_,clk);
    
endmodule
