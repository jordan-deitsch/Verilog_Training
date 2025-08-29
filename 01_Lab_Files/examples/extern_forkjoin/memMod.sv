module memMod(mem_if a); // Uses just the interface keyword
   logic avail;

   task a.Read (logic[7:0] raddr); // Read method
      $display("read memory @ %0h", raddr);
   endtask

   task a.Write(logic[7:0] waddr);
      $display("write memory @ %0h", waddr);
   endtask

endmodule
