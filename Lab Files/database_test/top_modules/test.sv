//********************
// Top level module that creates the UVM test

module test;

 router_env_pkg::router_env env;

 initial  begin
   // delay this initial block to ensure execution after
   // initial block in module top
   #1;
   env = new();
   env.build();
   env.connect();
   env.run();
   env.report();
   $finish();
 end
endmodule
