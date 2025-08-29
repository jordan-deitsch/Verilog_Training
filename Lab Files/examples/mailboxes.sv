module mailboxes;
  mailbox #(int) m = new();  // create mailbox
 
  task t1();
    for(int i = 0; i<4; i++) begin
     m.put(i);
     $display("T1 sent: %0d",i);
     #5;
    end     
  endtask
  task t2();
  int temp;
    while(1) begin
     m.get(temp);
     $display("T2 received: %0d",temp);
    end
  endtask

  initial begin
    fork
      t1();
      t2();
    join_none
    #0;
  end
endmodule
