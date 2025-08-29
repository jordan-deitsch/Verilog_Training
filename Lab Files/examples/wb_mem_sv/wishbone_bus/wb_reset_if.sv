
// Wishbone bus reset interface
// Does power-on reset
// Has methods to generate reset and to wait for reset
// Mike Baird

interface wb_reset_if( input bit clk, output bit rst );

//--------------------------------
// Power on reset 
 initial begin
   rst = 1;
   repeat(5) @ (posedge clk) ;
   rst = 0;
 end
   
 
 task automatic reset_wb_bus();
   if(rst) // is reset under way?
     wait_wb_bus_reset(); // wait until done
   else begin // reset bus
     rst = 1;
     repeat(5) @ (posedge clk) ;
     rst = 0;
   end
 endtask

 task automatic wait_wb_bus_reset();
   wait (!rst)
    @ (posedge clk); // wait for one more clk cycle
 endtask
 
 task automatic wait_for_wb_bus_reset();
   wait(rst);
 endtask
 
 
endinterface
