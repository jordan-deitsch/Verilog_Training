// test module
//-----------------

module test;
import wishbone_pkg::*;

  // LAB - Declare the shadow mem associative array
  bit[31:0] shadow_mem[bit[31:0]];

  initial begin
    // LAB - Declare transaction struct variable, address, and data variables
    wb_txn txn;
    bit[31:0] address;
    bit[31:0] data;

    // LAB - Wait for reset signal to go low
    @(negedge top.wb_bfm.rst);

    // LAB - Write 10  data values to 10  addresses, also storing into
    //       the shadow mem.


    //initialize address
    address = 0;
    for(int i=0; i <10; i++) begin
      shadow_mem[address] = i;  // write shadow mem
      // setup txn for write
      txn.adr = address;
      txn.data = i;
      txn.txn_type = WRITE;
      txn.count = 1;
      txn.byte_sel[3:0] = 4'b1111;
      // Write Wishbone mem
      top.wb_bfm.wb_write_cycle(txn);
      // increment address
      address += 4;
    end

    foreach (shadow_mem[addr]) begin
      // setup txn for read
      txn.adr = addr;
      txn.data = 32'bx;
      txn.txn_type = READ;
      txn.count = 1;
      txn.byte_sel[3:0] = 4'b1111;
      // Read Wishbone mem
      top.wb_bfm.wb_read_cycle(txn);
      // check read result against shadow mem
      if (txn.data === shadow_mem[addr]) begin
        $display("Memory passed at address %x",addr);
      end else begin
        $display("Memory failed at address %x -- expected %x, got %x",addr, shadow_mem[addr], txn.data[0]);
      end
    end
    $finish;
  end


endmodule
