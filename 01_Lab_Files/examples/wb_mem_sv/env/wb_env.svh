class wb_env;
  // mailbox handles
  mailbox #(wb_txn) gen2drv;
  mailbox #(wb_txn) mon2sb;
  // component handles
  stim_gen       s_gen;
  wb_bfm_driver  driver;
  wb_bfm_monitor monitor;
  mem_checker    mem_sb;

  function void build();
    // create mailboxe objects
    gen2drv = new(1);
    mon2sb  = new();
    // create component objects
    s_gen   = new();
    driver  = new();
    mem_sb  = new();
    monitor = new();
  endfunction

  function void connect();
    // connect up gen2drv mailbox
    s_gen.set_mb_handle(gen2drv);
    driver.set_mb_handle(gen2drv);
    // connect up mon2sb mailbox
    monitor.set_mb_handle(mon2sb);
    mem_sb.set_mb_handle(mon2sb);
    // connect virtual interfaces
    driver.set_v_if(v_wb_bfm);
    monitor.set_v_if(v_wb_bfm);
  endfunction

  task run();
    // start run methods in components
    fork
      driver.run();
      monitor.run();
      mem_sb.run();
    join_none 
    s_gen.run();
    disable fork;  // kill off other processes
  endtask

  function void report();
    mem_sb.report();
  endfunction
endclass
