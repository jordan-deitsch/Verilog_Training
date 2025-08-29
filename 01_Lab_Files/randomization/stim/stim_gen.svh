//-------------------------------------------
// stimulus generator
// generates Packets for the router
//
import analysis_pkg::verbosity;

class stim_gen;

 mailbox #(Packet_base) gen2drv[ROUTER_SIZE];  // mailbox handles

 int num_to_send = 1000;
  
 // LAB: Add your run() task here
   
endclass
