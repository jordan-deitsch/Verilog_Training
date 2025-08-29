package wishbone_pkg;

  typedef enum integer {NONE, WRITE, READ, RMW, WAIT_IRQ } wb_txn_t;

  typedef struct packed {
    wb_txn_t  txn_type;
    bit[31:0] adr;
    logic[31:0] data;
    int unsigned count;
    bit[7:0] byte_sel;
  } wb_txn;

  mailbox #(wb_txn) mon_mb = new();
  int in_flight = 0;

  task automatic ready_to_finish();
    wait (in_flight == 0) $finish();
  endtask

  task check_mem();
   bit[31:0] shadow_mem[bit[31:0]];
   wb_txn txn;
   bit[31:0] data;
   forever begin
    // LAB - Add code to get a transaction from the mon_mb mailbox and decrement in_flight
    mon_mb.get(txn);
    in_flight--;
    case (txn.txn_type)
      WRITE: shadow_mem[txn.adr] = txn.data;
      READ: begin
        if (txn.data === shadow_mem[txn.adr]) begin
          $display("Memory passed at address %x",txn.adr);
        end else begin
          $display("Memory failed at address %x -- expected %x, got %x",txn.adr, shadow_mem[txn.adr], txn.data[0]);
        end
      end
    endcase
   end // forever
  endtask

endpackage
