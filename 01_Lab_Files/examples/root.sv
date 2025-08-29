typedef struct{ logic [9:0] addr;
                logic[31:0] data;
              } global_pkt;
global_pkt root_pkt;

task global_task (input global_pkt in1);
  $display($stime,,"addr: %h, data: %h",in1.addr, in1.data);
endtask

module test;

global_pkt b;

local1 U1();

initial
  begin
   #10; 
   b.data = 1;
   b.addr = 1;
   global_task(b);
  end
endmodule

module local1;
logic [7:0] x;

global_pkt y;

initial
  begin
   #20; 
   y.data = 2;
   y.addr = 2;
   global_task(y);
   
   #20; 
   $root.root_pkt.data = 3;
   $root.root_pkt.addr = 3;
   global_task($root.root_pkt);
   
  end

endmodule

