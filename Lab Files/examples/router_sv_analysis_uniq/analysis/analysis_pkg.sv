package analysis_pkg;
import test_params_pkg::ROUTER_SIZE;
import txn_pkg::*;

  typedef enum  {LOW = 100, MEDIUM = 200, HIGH = 300, DEBUG = 400} verbosity_t;

  verbosity_t verbosity = MEDIUM;


 `include "whdl_ooo_comparator.svh"
 `include "comp_sb.svh"
 `include "router_coverage.svh"
 `include "coverage_sb.svh"

endpackage
