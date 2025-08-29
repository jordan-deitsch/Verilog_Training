


//program
module
p1(  input [7:0] cin, 
    output [7:0] cout,  
     input cclk );

clocking c @(posedge cclk);
  output cout;
  input cin;
endclocking
 

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


//endprogram
endmodule

module top;
logic[7:0] cout;
bit cclk ;
logic [7:0] cin = 0;

p1 p1 (.*);

initial
  fork
    forever #10 cclk = !cclk;
  join

initial forever begin #5 cin = cin +1;  end

//initial $monitor($stime,,"addr: %h, data: %h, cs: %b, rw_: %d, clk: %b",addr,data,cs,rw_,clk);
    
endmodule
