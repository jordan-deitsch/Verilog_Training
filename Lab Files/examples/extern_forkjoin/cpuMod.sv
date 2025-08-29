
module cpuMod(simple_bus b);
   enum {read, write} instr;
   logic [7:0] sel, waddr;
   int raddr, data;

   always @(posedge b.clk)
      if (instr == read)
         b.Read(sel, raddr, data); // call the slave method via the interface
      else
         b.Write(waddr);
endmodule
