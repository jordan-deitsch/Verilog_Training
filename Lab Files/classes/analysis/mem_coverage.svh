
//-------------------------------------------
// coverage object
// tracks functional coverage

class mem_coverage;

  wb_txn txn;

  covergroup cg;
    address_cp: coverpoint txn.adr iff (txn.txn_type == READ) {
      bins lowRange = { [0 : 32'h00030000]};
      bins hiRange  = { [32'h000a0000 : 32'h000fffff]};
    }
  endgroup

  function new();
    cg = new();
  endfunction

  virtual function void sample(wb_txn t);
    txn = t;
    cg.sample();
  endfunction

  virtual function real get_coverage();
    return cg.get_coverage();
  endfunction
endclass

