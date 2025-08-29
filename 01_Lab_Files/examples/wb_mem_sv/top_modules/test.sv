// test module
//---------------------

module test;
import env_pkg::wb_env;

 wb_env env;
 
 initial  begin
   env = new();  // create environment
   
   // wait for the bus reset
   wishbone_pkg::v_wb_reset.wait_wb_bus_reset();
   
   // call env methods
   env.build();
   env.connect();
   env.run();
   env.report();
   $finish();
 end
  
endmodule
