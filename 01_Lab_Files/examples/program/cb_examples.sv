


//program
module
p1(  input [7:0] cin, dcin, cin1,
    output [7:0] cout, cout2, dcout, cout1,
     input cclk, dclk );

clocking c @(posedge cclk);
  output cout;
  input cin;
endclocking
 
default clocking dc @(posedge dclk);
  output dcout;
  input dcin;
endclocking

clocking c1 @(posedge cclk);
  default input #10ps output #15ps;
  output cout1, cout2;
  input cin1;
endclocking
 

logic[7:0] s_cin;

initial
begin
     @(c);				// Advance to next cclk event
     c.cout <= 1;			// SynchDrive ( Updates on next cclk event )
     @(c);				// Advance to next cclk event
     c.cout <= 2; 		      	// SynchDrive
     @(c); 	      	      	      	      	
     c.cout <= 3; 		      	// Intra-procedural delay of 1 cycle then update
     @(c);				// 
     c.cout <= 4; 		      	// Intra-procedural delay of 1 cycle then update
     @(c);				// 
end

initial
begin
     @(c1);				// Advance to next cclk event
     c1.cout1 <= 1;			// SynchDrive ( Updates on next cclk event )
     @(negedge cclk);
     c1.cout1 <= 2; 		      	// SynchDrive
     @(negedge cclk);
     c1.cout1 <= 3; 		      	// Intra-procedural delay of 1 cycle then update
     @(c1);				// 
     c1.cout1 <= 4; 		      	// Intra-procedural delay of 1 cycle then update
     @(c1);				// 
end


initial
begin
     @(dc);				// Advance to next dclk event
     ##1 c1.cout2 <= 1;			// SynchDrive ( Updates on next dclk event )
     ##1;
      dc.dcout <= ##1 2; 		// Intra-procedural delay of 1 cycle then update
      	      	      	      	      	// but does NOT block thread
     ##4;
end


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
