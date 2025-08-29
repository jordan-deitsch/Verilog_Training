//------------------------
// environment class for rtl router testbench
//
class router_env;

 // stimulus component handles
 stim_gen s_gen;
 rtr_driver  r_driver[ROUTER_SIZE];
 mailbox #(Packet_base) drv2sb;
 mailbox #(Packet_base) gen2drv[ROUTER_SIZE];
 
 // monitor component handles
 rtr_monitor r_monitor[ROUTER_SIZE];
 mailbox #(Packet_base) mon2cov;
 mailbox #(Packet_base) mon2sb;

 // analysis component handles
 comp_sb s_board;
 coverage_sb cov_sb;

 virtual function void build();
  $display("Router size = %0dx%0d",ROUTER_SIZE,ROUTER_SIZE);    
  
  s_gen = new();
  s_board = new();
  cov_sb  = new();
  mon2cov  = new(1);
  mon2sb  = new(1);
  drv2sb  = new(1);

  for(int i = 0; i < ROUTER_SIZE; i++) begin
   // Create the drivers
   r_driver[i] = new(i);
   // Create the monitors
   r_monitor[i] = new(i);   
   // create buffers
   gen2drv[i] = new(1);
  end
 endfunction

 function void connect();
  for(int i = 0; i < ROUTER_SIZE; i++) begin
   // connect up drivers to stimulus generator buffers
   r_driver[i].gen2drv = gen2drv[i];
   
   // connect up s_gen to buffers
   s_gen.gen2drv[i] = gen2drv[i];
   
   r_monitor[i].mon2cov = mon2cov;
   r_monitor[i].mon2sb  = mon2sb;
 
   r_driver[i].drv2sb = drv2sb;
  end
  s_board.mb_0 = drv2sb;
  s_board.mb_1 = mon2sb;
  cov_sb.mon2cov = mon2cov;
 endfunction


  task run();
    for(int i=0; i<ROUTER_SIZE;i++) begin
      int j = i;
      fork
        r_driver[j].run();
        r_monitor[j].run();
      join_none
    end
    fork
      s_board.run();
      cov_sb.run();
    join_none 
    s_gen.run();
//    #100000;
    disable fork;  
  endtask

  function void report();
    s_board.report();
    cov_sb.report();
  endfunction

endclass
