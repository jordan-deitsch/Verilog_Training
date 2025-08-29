// test module
//------------------

module test();
import wishbone_pkg::*;

  task automatic gen_write_txn(bit[31:0] address, bit[31:0] data);
    top.wb_bfm.wb_write_cycle(data, address);
  endtask

  task automatic gen_read_txn(bit[31:0] address, ref bit[31:0] data);
    top.wb_bfm.wb_read_cycle(data, address);
  endtask

  task automatic generate_stimulus();
    bit[31:0] address = 0;
    bit[31:0] data;
    for(int i=0; i <10; i++) begin
      data = i;
      // increment address
      in_flight++;
      gen_write_txn(address, data);
      in_flight++;
      gen_read_txn(address, data);
      address += 4;
    end
    wishbone_pkg::ready_to_finish();
  endtask

  // Lab:  write monitor() task




 initial begin
   @(negedge top.wb_bfm.rst);
    // LAB - fork tasks



  end

endmodule
