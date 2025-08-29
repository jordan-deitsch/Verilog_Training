
//-------------------------------------------
// driver for rtl router
// transactor for input of router
// 1 driver per router port
//
class rtr_driver;
 
 mailbox #(Packet_base) gen2drv;  // mailbox handle
 mailbox #(Packet_base) drv2sb;   // mailbox handle

 virtual router_bfm #(`ROUTER_SIZE) v_r_bfm;

 int m_id;

 function new( int id );
  m_id = id; // set id
 endfunction

 task run();
  Packet stim_txn;
  Packet_base temp;
  v_r_bfm = test_params_pkg::v_r_bfm; // set virtual if
  forever begin
   gen2drv.get(temp);
   $cast(stim_txn, temp); // cast so can access all properties
   v_r_bfm.write_router(stim_txn.src_id,  stim_txn.dest_id, 
                        stim_txn.payload, stim_txn.pkt_id );
   drv2sb.put(stim_txn);  // broadcast txn
  end
 endtask
endclass 
