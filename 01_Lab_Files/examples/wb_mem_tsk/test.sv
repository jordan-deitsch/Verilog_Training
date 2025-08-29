// test module
//------------------

module test();
import wishbone_pkg::*;


 initial begin
   @(negedge top.wb_bfm.rst);
   generate_stimulus();
   check_mem();
   $finish();
 end

  bit[31:0] shadow_mem[bit[31:0]];

  // LAB - gen_write_txn
  task automatic gen_write_txn(bit[31:0] address, bit[31:0] data);
    shadow_mem[address] = data;
    top.wb_bfm.wb_write_cycle(data, address);
  endtask

  // LAB - gen_read_txn
  task automatic gen_read_txn(bit[31:0] address, ref bit[31:0] data);
    top.wb_bfm.wb_read_cycle(data, address);
  endtask


  task automatic generate_stimulus();
    bit[31:0] address = 0;
    bit[31:0] data;
    for(int i=0; i <10; i++) begin
      data = i;
      // increment address
      gen_write_txn(address, data);
      address += 4;
    end
  endtask

  task automatic check_mem();
    bit[31:0] data;
    foreach (shadow_mem[addr]) begin
        gen_read_txn(addr, data);
        if (data === shadow_mem[addr]) begin
          $display("Memory passed at address %x",addr);
        end else begin
          $display("Memory failed at address %x -- expected %x, got %x",addr, shadow_mem[addr], data);
        end
    end
  endtask
endmodule
