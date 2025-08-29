
package alu_pkg;

  typedef enum {ADD, SUB, MUL, DIV} op_type_t;

  typedef struct {
     op_type_t mode;
     shortint unsigned val1;
     shortint unsigned val2;
     int result; 
     int txn_id;
  } alu_txn;

  mailbox #(alu_txn) mon_mb = new(); 
  int in_flight = 0;

  task automatic ready_to_finish();
    wait (in_flight == 0) $finish();
  endtask

  function automatic alu_txn create_txn(op_type_t op, shortint v1, shortint v2);
    alu_txn txn;
    txn.val1 = v1;
    txn.val2 = v2;
    txn.mode = op;
    return txn;
  endfunction

  task check_result ();
    alu_txn result_txn;
    int expected_result;

    forever begin
      mon_mb.get(result_txn);
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
      in_flight--;
    end
  endtask
endpackage
