
class result_checker;
  mailbox #(alu_txn) mon_mb;

  task run ();
    alu_txn result_txn;
    int expected_result;

    forever begin
      mon_mb.get(result_txn);
      in_flight--;

      case (result_txn.mode)
        ADD: expected_result = result_txn.val1 + result_txn.val2;
        SUB: expected_result = result_txn.val1 - result_txn.val2;
        MUL: expected_result = result_txn.val1 * result_txn.val2;
        DIV: expected_result = result_txn.val1 / result_txn.val2;
      endcase

      if (result_txn.result == expected_result)
        $display("ALU operation PASSED:  %d %s %d = %0d ",result_txn.val1,
          result_txn.mode.name(), result_txn.val2, result_txn.result );
      else begin
        $write  ("ALU operation FAILED:  %d %s %d = %0d",result_txn.val1, 
          result_txn.mode.name(), result_txn.val2, result_txn.result );
        $display(" expected %0d, got %0d", expected_result, result_txn.result);
      end
    end
  endtask

  // Methods for setting properties
  function void set_mb_handle(mailbox #(alu_txn) mb);
    mon_mb = mb;
  endfunction


endclass
