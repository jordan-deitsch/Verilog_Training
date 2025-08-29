import alu_pkg::op_type_t;
import alu_pkg::alu_txn;

interface alu_bfm_if(
  input bit clk
  );

// alu ports
  shortint unsigned val1, val2;
  bit valid_i;
  op_type_t mode;
  bit valid_o;
  int result;

// not conntected to the alu  
  int txn_id;
  
   // write task
// task write(input alu_txn stim_txn);
 task write(input op_type_t txn_mode,
            input shortint unsigned txn_val1,
            input shortint unsigned txn_val2,
            input int txn_txn_id = 0);
    @ (negedge clk)
    val1 <= txn_val1;
    val2 <= txn_val2;
    mode <= txn_mode;        
    txn_id = txn_txn_id;
    valid_i <= 1;  // set valid_i
    @ (posedge clk)
    valid_i <= 0;  // clear valid_i
 endtask

 // monitor task
 task monitor_alu(output op_type_t txn_mode,
              output shortint unsigned txn_val1,
              output shortint unsigned txn_val2,
              output int txn_txn_id,
              output int txn_result);
  forever begin
   @ (negedge clk)
   if(valid_o) begin
    txn_result = result;
    txn_val1 = val1;
    txn_val2 = val2;
    txn_mode = mode;
    txn_txn_id = txn_id;
    return;
   end
  end  
 endtask
    
endinterface
