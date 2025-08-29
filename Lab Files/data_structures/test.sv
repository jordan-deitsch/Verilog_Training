// test module
//-----------------

module test;

  // LAB - Import package



  // LAB - Declare the shadow mem associative array



  initial begin
    // LAB - Declare transaction struct variable, address, and data variables





    // LAB - Wait for reset signal to go low





    // This code writes 10  data values to 10  addresses, also storing that data in
    // the shadow mem.
    // Start by initializing address to zero...
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



    // LAB - Check the data in Wishbone memory against the shadow memory







    $finish;
  end


endmodule
