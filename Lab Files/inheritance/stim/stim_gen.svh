//-------------------------------------------
// stimulus generator
// generates Packets for the router
//
import analysis_pkg::verbosity;

class stim_gen;

 mailbox #(Packet_base) gen2drv[ROUTER_SIZE];  // mailbox handles

 int num_to_send = 1000;
  
 task run();
  Packet txn;
  
  if(verbosity >= analysis_pkg::MEDIUM)
    $display("stim_gen:  Creating %0d Packets\n", num_to_send); 
  for(int i = 1; i <= num_to_send; i++) begin
   txn = new();
   if(!txn.randomize())
      if(verbosity >= analysis_pkg::MEDIUM)
            $display("stim_gen:  Randomization error");
   txn.pkt_id = i; // set Packet id
   gen2drv[txn.src_id].put(txn);
  end
 endtask
   
endclass
