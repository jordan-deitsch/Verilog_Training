
package wishbone_pkg;
import test_params_pkg::*;

  typedef enum {NONE, WRITE, READ, RMW, WAIT_IRQ } wb_txn_t;
  typedef enum {IS_OK, NOT_OK} status_e;  
  
  virtual wb_syscon_bfm_if v_wb_bfm;
  virtual wb_reset_if v_wb_reset;

  `include "wb_txn.svh"
  `include "stim_gen.svh"

  
  `include "wb_bfm_driver.svh"
  
  `include "wb_bfm_monitor.svh"

endpackage
