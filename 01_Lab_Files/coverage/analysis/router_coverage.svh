
//-------------------------------------------
// coverage object
// tracks functional coverage

class router_coverage;

  Packet temp_txn;

  // LAB: Add your cov1 covergroup here
  
  

  function new();

  endfunction


  virtual function void sample(Packet p);
    temp_txn = p;
    cov1.sample();
  endfunction


  virtual function real get_coverage();
    return cov1.get_coverage();
  endfunction

endclass

