// test module
//---------------------

module test;
import env_pkg::wb_env;

 // LAB:  declare environment handle
 


 initial  begin
   
   //LAB:  create environment object
   

   // wait for the bus reset
   wishbone_pkg::v_wb_reset.wait_wb_bus_reset();
   
   
   // LAB:  call env methods



   $finish();
 end
  
endmodule
