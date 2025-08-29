class wb_bfm_monitor;

  mailbox #(wb_txn) mon2sb;
  virtual wb_syscon_bfm_if m_wb_bfm;

  task run();
    wb_txn txn, cov_txn;
    int txn_type;
    forever begin
      txn = new();
      // get a txn
      m_wb_bfm.monitor_txn(txn.data, txn.adr, txn.txn_type);
      mon2sb.put(txn); 
    end
  endtask

  // Methods for setting properties
  function void set_mb_handle(mailbox #(wb_txn) mb);
    mon2sb = mb;
  endfunction

  function void set_v_if(virtual wb_syscon_bfm_if v_if);
    m_wb_bfm = v_if;
  endfunction

endclass
