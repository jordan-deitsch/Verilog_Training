class mem_checker;

 mailbox #(wb_txn) mon2sb;

 bit[31:0] shadow_mem[bit[31:0]];
 int txn_count;
 int error_count;
  
 task run();
  wb_txn txn, expected_txn;
  bit[31:0] data;
  expected_txn = new();
  forever begin
   mon2sb.get(txn);
   txn_count++;
   if(verbosity >= HIGH)
     $display("MEM_CHECK: Recived a txn, txn cnt: %0d, %s\n",txn_count, txn.convert2string());
   case (txn.txn_type)
    WRITE: shadow_mem[txn.adr] = txn.data[0];
    READ: begin
     expected_txn.copy(txn);
     expected_txn.data[0] = shadow_mem[txn.adr];
     if (expected_txn.compare(txn)) begin
       if(verbosity >= MEDIUM)
         $display("MEM_CHECK:  Memory passed at address %x",txn.adr);
     end else begin
       if(verbosity >= LOW)
         $display("MEM_CHECK: Memory failed at address %x:\nExpected:\n%s\nActual:\n%s",
             txn.adr, expected_txn.convert2string(), txn.convert2string());
       error_count++;
     end
    end
   endcase
  end // forever
 endtask
  
 function void report();
   if(verbosity >= MEDIUM) begin
     $display("\n********************************");
     $display("  total transactions: %0d",txn_count);
     $display("  total errors:       %0d",error_count);
     $display("********************************\n"); 
   end
 endfunction

 // Methods for setting properties
 function void set_mb_handle(mailbox #(wb_txn) mb);
   mon2sb = mb;
 endfunction


endclass
