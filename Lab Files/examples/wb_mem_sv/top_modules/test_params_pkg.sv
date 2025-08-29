package test_params_pkg;

  // WISHBONE general master parameters
  parameter WB_AGENT_MASTER_ID = 1;

  // WISHBONE general slave parameters
  parameter SLAVE_ADDR_SPACE_SZ = 32'h00100000;
  
  // WISHBONE slave memory parameters
  parameter MEM_SLAVE_0_WB_ID = 0;  // WISHBONE bus slave id of wb slave memory 
  parameter MEM_SLAVE_1_WB_ID = 1;  // WISHBONE bus slave id of wb slave memory 
  parameter MEM_SLAVE_0_SIZE = 32'h00100000;    // size in bytes of wb slave memory
  parameter MEM_SLAVE_1_SIZE = 32'h00100000;    // size in bytes of wb slave memory
  parameter MEM_SLAVE_0_WD_SIZE = 18;    // 2**(slave_mem_wd_size) = size in words of wb slave memory
  parameter MEM_SLAVE_1_WD_SIZE = 18;    // 2**(slave_mem_wd_size) = size in wrods of wb slave memory
    
endpackage
