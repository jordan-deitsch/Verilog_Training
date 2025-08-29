
//-------------------------------------------
// monitor for rtl router
// transactor for output of router
// 1 monitor per router output port
//
class rtr_monitor;

 mailbox #(Packet_base) mon2sb;   // mailbox handle
 mailbox #(Packet_base) mon2cov;  // mailbox handle

 int m_id;
 virtual router_bfm #(ROUTER_SIZE) v_r_bfm;

 function new( int id );
  m_id = id; // set id
 endfunction

 task run();
  Packet mon_txn;
  v_r_bfm = test_params_pkg::v_r_bfm; // set virtual if
  forever begin
   mon_txn = new();
   v_r_bfm.read_router_port(m_id, mon_txn.src_id,
                            mon_txn.dest_id, mon_txn.payload,
                            mon_txn.pkt_id);
   mon2sb.put(mon_txn);
   mon2cov.put(mon_txn);
  end
 endtask

endclass
