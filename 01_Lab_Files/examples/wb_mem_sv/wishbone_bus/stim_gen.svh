
class stim_gen;

  mailbox #(wb_txn) gen2drv;
  parameter num_ops = 11;

  function new();
  endfunction

  task run();
    wb_txn txn;
    bit[31:0] address;
    logic[31:0] data[1];
    repeat(num_ops) begin
      address = $urandom_range(0, 32'h000ffffc);
      data[0] = $urandom();
      txn = new();
      txn.init_txn(WRITE, address, data);
      gen2drv.put(txn);
      txn = new();
      txn.init_txn(READ, address, data);
      gen2drv.put(txn);
    end
  endtask

  // Methods for setting properties
  function void set_mb_handle(mailbox #(wb_txn) mb);
    gen2drv = mb;
  endfunction

endclass
