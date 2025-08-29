
package analysis_pkg;
import wishbone_pkg::*;

  typedef enum  {LOW = 100, MEDIUM = 200, HIGH = 300, DEBUG = 400} verbosity_t;

  verbosity_t verbosity = MEDIUM;

  `include "mem_checker.svh"
  `include "mem_coverage.svh"
  `include "coverage_sb.svh"

endpackage
