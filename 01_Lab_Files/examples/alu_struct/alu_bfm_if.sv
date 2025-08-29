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
  shortint unsigned result;

// not conntected to the alu  
  int txn_id;
  
   // write task
 task write(input alu_txn stim_txn);
    @ (negedge clk)
    val1 <= stim_txn.val1;
    val2 <= stim_txn.val2;
    mode <= stim_txn.mode;        
    valid_i <= 1;  // set valid_i
    @ (posedge clk)
    valid_i <= 0;  // clear valid_i
 endtask

 // monitor task
 task monitor(output alu_txn rsp);
  forever begin
   @ (negedge clk)
   if(valid_o) begin
    rsp.result = result;
    rsp.val1 = val1;
    rsp.val2 = val2;
    rsp.mode = mode;
    return;
   end
  end  
 endtask

    
endinterface
