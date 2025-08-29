


//program
module
p1(  input [7:0] cin, dcin,
    output [7:0] cout, dcout,
     input cclk, dclk );

 
default clocking dc @(posedge dclk);
  default input #10ps output #15ps;
  output dcout;
  input dcin;
endclocking

clocking c @(posedge cclk);
  default input #10ps output #15ps;
  output cout;
  input cin;
endclocking
 

logic[7:0] s_cin;


initial
begin
     @(dc);				// Advance to next dclk event
     ##1 c.cout <= 1;			// SynchDrive ( Updates on next dclk event )
     ##1;
      dc.dcout <= ##1 2; 		// Intra-procedural delay of 1 cycle then update
      	      	      	      	      	// but does NOT block thread
     ##4;
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
