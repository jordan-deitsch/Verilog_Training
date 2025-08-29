
class monitor;
  mailbox #(alu_txn) mon_mb;
  virtual alu_bfm_if v_if;

  task run();
    alu_txn txn;
    forever begin
      txn = new();
      v_if.monitor_alu(txn.mode, txn.val1, txn.val2,
                   txn.txn_id, txn.result);
      mon_mb.put(txn);
    end
  endtask

  // Methods for setting properties
  function void set_mb_handle(mailbox #(alu_txn) mb);
    mon_mb = mb;
  endfunction

  function void set_v_if(virtual alu_bfm_if v_if_arg);
    v_if = v_if_arg;
  endfunction

 endclass
