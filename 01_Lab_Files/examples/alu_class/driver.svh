class driver;
 
  mailbox #(alu_txn) drv_mb;
  virtual alu_bfm_if v_if;

  task run();
    alu_txn txn;
    forever begin
      drv_mb.get(txn);
      v_if.write(txn.mode,txn.val1, txn.val2);
    end
  endtask

  // Methods for setting properties
  function void set_mb_handle(mailbox #(alu_txn) mb);
    drv_mb = mb;
  endfunction

  function void set_v_if(virtual alu_bfm_if v_if_arg);
    v_if = v_if_arg;
  endfunction

endclass
