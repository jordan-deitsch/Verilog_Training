// module test
//-----------------

module test();
import alu_pkg::*;

  parameter num_ops = 10;
 
  initial
    fork
      generate_stimulus(num_ops);
      monitor();
      check_result();
    join_none;

  // tasks

  task generate_stimulus(int unsigned n);
    alu_txn txn;
    shortint unsigned operand1;
    shortint unsigned operand2;
    op_type_t op;
    for (int i = 0; i < n; i++) begin
      operand1 = $urandom_range(0, 1000);
      operand2 = $urandom_range(0, 1000);
      op = op_type_t'($urandom() % 4);
      // write alu
      top.alu_bfm_if.write(op, operand1, operand2);
      in_flight++;
    end
    alu_pkg::ready_to_finish();
  endtask

  task automatic monitor();
    alu_txn txn;
    forever begin
      top.alu_bfm_if.monitor_alu(txn.mode, txn.val1,
              txn.val2, txn.txn_id, txn.result);
      mon_mb.put(txn);
    end
  endtask


endmodule
