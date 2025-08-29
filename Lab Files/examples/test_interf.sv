interface simple_bus (input bit clk, rst, enable); // Define the interface
   logic req, gnt;
   logic [7:0] addr, data;
   logic [1:0] mode;
   logic start, rdy;
   task junk;
     @(posedge enable)
       $display("Posedge enabls");
   endtask
endinterface: simple_bus

module memMod(simple_bus a); // Uses just the interface
   logic avail;
   always @(posedge a.clk) // the clk signal from the interface
     begin
      a.gnt <= a.req & avail; // a.req is in the ’simple_bus’ interface
      a.junk;
     end
endmodule


module top;
   logic clk = 0;
   bit rst = 0;
   bit enable = 0;
   simple_bus sb_intf1(clk, rst, enable); // Instantiate the interface
   simple_bus sb_intf2(clk); // Instantiate the interface
   memMod mem1(.a(sb_intf1)); // Connect bus 1 to memory 1
   memMod mem2(.a(sb_intf2)); // Connect bus 2 to memory 2
endmodule
