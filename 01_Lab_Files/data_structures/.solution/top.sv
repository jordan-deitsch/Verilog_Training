//  Top level module for a wishbone system with bus connection
// multiple masters and slaves
// Mike Baird
//----------------------------------------------
module top;

// LAB - import the Wishbone package
import wishbone_pkg::*;

  //-----------------------------------   
  // WISHBONE interface instance
  // provides the system interconnect and the WISHBONE arbitration
  // Supports up to 8 masters and up to 8 slaves
  wishbone_bus_syscon_if wb_bfm();
  
  //-----------------------------------   
  //  wishbone 0, slave 0:  00000000 - 000fffff
  //  this is 1 Mbytes of memory
  wb_slave_mem  #(18) wb_s_0 (
    // inputs
    .clk ( wb_bfm.clk ),
    .rst ( wb_bfm.rst ),
    .adr ( wb_bfm.s_addr ),
    .din ( wb_bfm.s_wdata ),
    .cyc ( wb_bfm.s_cyc ),
    .stb ( wb_bfm.s_stb[0] ),
    .sel ( wb_bfm.s_sel[3:0] ),
    .we  ( wb_bfm.s_we  ),
    // outputs
    .dout( wb_bfm.s_rdata[0] ),
    .ack ( wb_bfm.s_ack[0] ),
    .err ( wb_bfm.s_err[0] ),
    .rty ( wb_bfm.s_rty[0] )
  );



  
endmodule
