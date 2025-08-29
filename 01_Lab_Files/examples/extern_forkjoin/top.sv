module top;
   logic clk = 0;
   mem_if mem_intf(clk); 		// Instantiate the interface
   memMod mem1(.a(mem_intf.slave)); 	// First memory using slave interface
   memMod mem2(.a(mem_intf.slave)); 	// second memory
   cpuMod  cpu(.b(mem_intf.master)); 	// CPU using the master interface
endmodule
