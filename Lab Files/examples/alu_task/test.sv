// test module
//--------------------

module test();
 import alu_pkg::*;

 parameter num_ops = 10;
 shortint unsigned expected[];
 shortint unsigned operand1[];
 shortint unsigned operand2[];
 op_type_t ops[];


 initial begin
   generate_stimulus(num_ops);
   do_test(num_ops);
   $finish();
 end

 function automatic void generate_stimulus(int unsigned n);
   operand1 = new[n];
   operand2 = new[n];
   ops = new[n];
   expected = new[n];

   for (int i = 0; i < n; i++) begin
     int j, k;
     operand1[i] = $urandom() % 1000;
     operand2[i] = $urandom() % 1000;
     ops[i] = op_type_t'($urandom() % 4);
     case(ops[i])
       ADD: expected[i] =  operand1[i] + operand2[i];
       SUB: expected[i] =  operand1[i] - operand2[i];
       MUL: expected[i] =  operand1[i] * operand2[i];
       DIV: expected[i] =  operand1[i] / operand2[i];
     endcase
   end
 endfunction

 function automatic alu_txn create_txn(op_type_t op, shortint v1, shortint v2);
   alu_txn txn;
   txn.val1 = v1;
   txn.val2 = v2;
   txn.mode = op;
   return txn;
 endfunction

 task automatic do_test(int unsigned n);
   shortint result;
   for (int i = 0; i < n; i++) begin
     drive_txn(ops[i], operand1[i], operand2[i]);
     get_result(result);
     if (result == expected[i])
       $display("ALU operation #%0d passed",i);
     else
       $display("ALU operation failed: expected %0d, got %-d", expected[i], result);
   end
 endtask

 task automatic drive_txn(op_type_t op, shortint v1, shortint v2);
  top.alu_bfm_if.write(op, v1,v2);
 endtask

 task automatic get_result(ref shortint result);
   alu_txn txn;
   top.alu_bfm_if.monitor_alu(txn.mode, txn.val1,
                        txn.val2,txn.txn_id,
                        txn.result);
   result = txn.result;
 endtask

endmodule
