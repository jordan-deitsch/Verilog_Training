class test_env;

  //component handles
  monitor mon;
  driver drv;
  stim_gen s_gen;
  result_checker chk;
  //mailbox handles
  mailbox #(alu_txn) mon_mb;
  mailbox #(alu_txn) drv_mb;

  function void build();
    // Create the components
    mon = new();
    drv = new();
    s_gen = new();
    chk = new();
    // Create the mailboxes
    mon_mb = new();
    drv_mb = new();
  endfunction

  function void connect();
    //  Connect the mailboxes to the internal handles
   mon.set_mb_handle(mon_mb);
   chk.set_mb_handle(mon_mb);
   s_gen.set_mb_handle(drv_mb);
   drv.set_mb_handle(drv_mb);
   // Connect the virtual interfaces
   mon.set_v_if(v_alu_bfm_if);
   drv.set_v_if(v_alu_bfm_if);
  endfunction

  task run();
    fork
      mon.run();
      chk.run();
      drv.run();
    join_none;
    s_gen.run(num_ops);
    disable fork;
  endtask

endclass
