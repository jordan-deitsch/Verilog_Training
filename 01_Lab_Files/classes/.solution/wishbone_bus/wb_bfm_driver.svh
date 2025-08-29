
//---------------------------------------------
// driver for the BFM wishbone bus interface

class wb_bfm_driver;

  mailbox #(wb_txn) gen2drv;
  virtual wb_syscon_bfm_if m_v_wb_bfm;
  
  task run();
    wb_txn txn;
    forever begin
      gen2drv.get(txn);
      case (txn.txn_type)
        WRITE: 
         begin
          m_v_wb_bfm.wb_write_cycle(txn.data, txn.adr, txn.count,
             .wb_master_id(test_params_pkg::WB_AGENT_MASTER_ID),.op_stat(txn.t_status));
         end
        READ :
         begin
          m_v_wb_bfm.wb_read_cycle(txn.data, txn.adr, txn.count,
            .wb_master_id(test_params_pkg::WB_AGENT_MASTER_ID), .op_stat(txn.t_status));
         end
        default: begin
          $display("DRIVER: Unsupported txn type received");
          txn.print();
         end
      endcase
    end
  endtask

  // Methods for setting properties
  function void set_mb_handle(mailbox #(wb_txn) mb);
    gen2drv = mb;
  endfunction

  function void set_v_if(virtual wb_syscon_bfm_if v_if);
    m_v_wb_bfm = v_if;
  endfunction
endclass
