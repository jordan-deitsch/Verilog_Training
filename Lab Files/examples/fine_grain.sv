module fine_grain;

process jobs[1:3];

initial
 fork
   one; two; three;
 join_none

 task one;
   jobs[1] = process::self();
   $display("task 1 running");
   #10;
   $display("task 1 exiting");
 endtask
 
 task two;
   jobs[2] = process::self();
   $display("task 2 sleeping");
   jobs[2].suspend();
//   #5;
   $display("task 2 exiting");
 endtask

 task three;
   jobs[3] = process::self();
   $display("task 3 awaiting completion of task 1");   
   jobs[1].await();
   $display("task 3 resuming task 2");   
   jobs[2].resume();
 endtask
 


  
endmodule
