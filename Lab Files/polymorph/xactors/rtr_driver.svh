
//-------------------------------------------
// driver for rtl router
// transactor for input of router
// 1 driver per router port
//
class rtr_driver;
 
 // LAB:  Declare mailbox handles




 virtual router_bfm #(`ROUTER_SIZE) v_r_bfm;

 int m_id;

 function new( int id );
  m_id = id; // set id
 endfunction

 task run();
  // LAB:  declare handles  


  v_r_bfm = test_params_pkg::v_r_bfm; // set virtual if
  forever begin
   
   //LAB:  Get Packet and cast

   
   
   v_r_bfm.write_router(stim_txn.src_id,  stim_txn.dest_id, 
                        stim_txn.payload, stim_txn.pkt_id );
   
   // LAB:  Send the Packet object to the scoreboard



  end
 endtask
endclass 
