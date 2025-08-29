
package alu_pkg;

  typedef enum {ADD, SUB, MUL, DIV} op_type_t;

  virtual alu_bfm_if v_alu_bfm_if;
  int in_flight = 0;
  
  task automatic ready_to_finish();
    wait (in_flight == 0) $finish();
  endtask

  parameter num_ops = 10;

  `include "alu_txn.svh"
  `include "monitor.svh"
  `include "driver.svh"
  `include "stim_gen.svh"
  `include "result_checker.svh"
  `include "test_env.svh"


endpackage
