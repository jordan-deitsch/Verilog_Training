// top level module for rtl alu
module top();
import alu_pkg::*;

parameter num_ops = 10;

  // generate the clock
  bit clk = 0;
  initial
   forever #50 clk = !clk;

    // alu_if instance
  alu_bfm_if alu_bfm_if(.clk(clk));

    // DUT instance
  alu_rtl alu (
    .val1(alu_bfm_if.val1),
    .val2(alu_bfm_if.val2),
    .mode(alu_bfm_if.mode),
    .clk(alu_bfm_if.clk),
    .valid_i(alu_bfm_if.valid_i),
    .valid_o(alu_bfm_if.valid_o),
    .result(alu_bfm_if.result)
    );
    

 initial begin
   alu_txn txn;
   shortint unsigned operand1[];
   shortint unsigned operand2[];
   op_type_t ops[];
   shortint unsigned expected[];

   operand1 = new[num_ops];
   operand2 = new[num_ops];
   ops = new[num_ops];
   expected = new[num_ops];

   for (int i = 0; i < num_ops; i++) begin
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

   for (int i = 0; i < num_ops; i++) begin
      txn.val1 = operand1[i];
      txn.val2 = operand2[i];
      txn.mode = ops[i];
      alu_bfm_if.write(txn);
      alu_bfm_if.monitor(txn);
      if (txn.result == expected[i])
        $display("ALU operation #%0d passed",i);
      else
        $display("ALU operation failed: expected %0d, got %-d", expected[i], txn.result);
   end
   $finish;
 end



endmodule
