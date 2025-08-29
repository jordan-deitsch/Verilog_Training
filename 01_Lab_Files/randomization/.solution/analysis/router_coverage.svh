
//-------------------------------------------
// coverage object
// tracks functional coverage

class router_coverage;

  Packet temp_txn;

  covergroup cov1;
   s: coverpoint temp_txn.src_id {
       bins src[ROUTER_SIZE] = {[0:ROUTER_SIZE-1]};
      }
   d: coverpoint temp_txn.dest_id {
       bins dest[ROUTER_SIZE] = {[0:ROUTER_SIZE-1]};
      }
   cross s, d;
  endgroup


  function new();
    cov1 = new();
  endfunction


  virtual function void sample(Packet p);
    temp_txn = p;
    cov1.sample();
  endfunction


  virtual function real get_coverage();
    return cov1.get_coverage();
  endfunction

endclass

