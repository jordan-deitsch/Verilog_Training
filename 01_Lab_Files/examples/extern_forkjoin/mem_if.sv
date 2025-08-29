interface mem_if (input bit clk); // Define the interface
   logic req, gnt;
   logic [7:0] addr, data;
   logic [1:0] mode;
   logic start, rdy;
   
   extern forkjoin task  Read(logic [7:0] sel, int addr, output int data); 
   extern forkjoin task Write(input logic[7:0] waddr);

   modport slave( input req, addr, mode, start, clk,
                             output gnt, rdy, inout data,
                             export task Read(), task Write());                       // export from module that defines the tasks
  
   modport master(input gnt, rdy, clk,
                              output req, addr, mode, start, inout data,
                              import task Read(logic [7:0] sel, int addr, output int data),
                                     task Write(input logic[7:0] waddr));       // import requires the full task prototype

endinterface: mem_if
