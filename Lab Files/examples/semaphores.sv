module semaphores;
  semaphore s1 = new(1);
  task t1();
    for(int i = 0; i<3; i++) begin
      s1.get(1);
      #5;
      $display("t1 has ownership of semaphore");
      s1.put(1);
      #5;
    end
  endtask
  task t2();
    for(int i = 0; i<3; i++) begin
      s1.get(1);
      #5;
      $display("t2 has ownership of semaphore");
      s1.put(1);
      #5;
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
