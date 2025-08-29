typedef struct{ logic[1:0] ad;} pkt;
typedef struct{ logic[0:1] ad;} bpkt;

// We use the bit-reversal to identify that the types
// actually change with the parameter type changes


module param_port(aa,bb,write,read,clk);
parameter type st = pkt;
input st aa; 
output st bb; 
input logic write, read, clk;

st pkt_array[15:0];

always@(posedge clk)
  if (write)
    pkt_array[aa.ad] = aa;
  else if (read)
    bb = pkt_array[aa.ad];  

endmodule

module tb;

parameter type stype = pkt;   //EDIT HERE to switch tb
logic write, read, clk;
stype aa, bb;

param_port #(.st(pkt))        // AND EDIT HERE to switch DUT
         DUT (.aa(aa), .bb(bb), .write(write), .read(read), .clk(clk));  
  
initial
  begin
    clk = 0;
    forever #20 clk = !clk;
  end
  
initial
  begin
    write = 0;
    read = 0;
    aa.ad = 0;
    @(negedge clk)
    aa.ad = 1;
    write = 1;
    @(negedge clk)  // write address 1
    aa.ad = 2;
    @(negedge clk)  // write address 2
    aa.ad = 3;
    @(negedge clk)  // write address 3
    write = 0;
    @(negedge clk)
    read = 1;
    aa.ad = 3;
    @(negedge clk)  // read address 3
    $display(bb.ad[0]); // different for pkt and bpkt
    aa.ad = 2;
    @(negedge clk)  // read address 2
    $display(bb.ad[0]);
    aa.ad = 1;
    @(negedge clk)  // read address 1
    $display(bb.ad[0]);
    #100 $stop;
  end 
  
endmodule


/*
//for pkt type
1
0
1

// for bpkt type
1
1
0


*/

