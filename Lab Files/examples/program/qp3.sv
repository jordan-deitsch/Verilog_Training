program p3(input [7:0]dcin, output [7:0] dcout, input dclk);
 
default clocking dc @(posedge dclk);
  default input #10ps output #15ps;
  output dcout;
  input dcin;
endclocking

logic[7:0] s_cin;


initial
begin
     ##2;			// Advance to next dclk event
         dc.dcout = ##1 8'h6;
     ##1 s_cin = dc.dcin;	// Capture dcin value sampled on last cclk
     ##4;
end


endprogram

module top;
logic[7:0] dcout;
bit dclk;
logic [7:0] dcin = 10;

p3 p3 (.*);

initial
    forever #20 dclk = !dclk;

initial forever begin #5 dcin = dcin +1; end

//initial $monitor($stime,,"addr: %h, data: %h, cs: %b, rw_: %d, clk: %b",addr,data,cs,rw_,clk);
    
endmodule
