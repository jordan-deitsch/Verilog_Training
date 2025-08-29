module task_2;
int global_a = 0,
    global_b = 1;

initial $monitor($stime," global_a: %0h, global_b: %0h",global_a, global_b);

initial
  begin
    #10 my_task(2,5);
    #10 my_task(8,8);
    #10 my_task(32'ha,32'hf);
    #10 my_task(32'hb,32'hb);
    #10 $finish;
  end



task automatic my_task( input int local_a,
                              int local_b);

$display("\n",$stime," Input args %0h,%0h",local_a,local_b);
if(local_a == local_b)
  begin
   $display($stime," Arguments are the same!");
   my_task(local_a-1,local_b+1);
   #5 $display($stime," Recursively changed args %0h,%0h to %0h,%0h.",local_a,local_b,local_a-1,local_b+1);
   return;
  end
global_a = local_a;
global_b = local_b;

endtask










endmodule
