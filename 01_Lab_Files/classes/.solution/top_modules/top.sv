//  Top level module for a wishbone system with bus connection
// multiple masters and slaves
// Mike Baird
//----------------------------------------------

module top;
import test_params_pkg::*;

  //-----------------------------------   
  // WISHBONE interface instance
  // provides the system interconnect and the WISHBONE arbitration
  // Supports up to 8 masters and up to 4 slaves
  wb_syscon_bfm_if wb_bfm(clk, rst);
  wb_reset_if wb_reset(clk, rst);
  
  //-----------------------------------   
  //  WISHBONE 0, slave 0 XXX00000 - XXX0fffff
  //  this is 1 Mbytes of memory
  wb_slave_mem  #(MEM_SLAVE_0_WD_SIZE, MEM_SLAVE_0_WB_ID, SLAVE_ADDR_SPACE_SZ)
   wb_s_0 (
    // inputs
    .clk ( clk ),
    .rst ( rst ),
    .adr ( wb_bfm.s_addr ),
    .din ( wb_bfm.s_wdata ),
    .cyc ( wb_bfm.s_cyc ),
    .stb ( wb_bfm.s_stb[MEM_SLAVE_0_WB_ID]   ),
    .sel ( wb_bfm.s_sel[3:0] ),
    .we  ( wb_bfm.s_we  ),
    // outputs
    .dout( wb_bfm.s_rdata[MEM_SLAVE_0_WB_ID] ),
    .ack ( wb_bfm.s_ack[MEM_SLAVE_0_WB_ID]   ),
    .err ( wb_bfm.s_err[MEM_SLAVE_0_WB_ID]   ),
    .rty ( wb_bfm.s_rty[MEM_SLAVE_0_WB_ID]   )
  );


  initial begin
    wishbone_pkg::v_wb_bfm = wb_bfm;
    wishbone_pkg::v_wb_reset = wb_reset;
  end
endmodule
