
class stim_gen;
 
  mailbox #(alu_txn) drv_mb;

  task run(int unsigned n);
    alu_txn txn;
    for (int i = 0; i < n; i++) begin
      txn = new();
      txn.init_txn(op_type_t'($urandom() % 4),
               $urandom_range(0, 1000),
               $urandom_range(0, 1000),
               i);
      // push the txn into buffer
      drv_mb.put(txn);
      in_flight++; //increment number outstanding txns
    end
    alu_pkg::ready_to_finish();
  endtask

  // Methods for setting properties
  function void set_mb_handle(mailbox #(alu_txn) mb);
    drv_mb = mb;
  endfunction

endclass
