typedef struct{ logic [9:0] addr;
                logic[31:0] data;
              } global_pkt;
global_pkt root_pkt;


module test;

typedef struct{ global_pkt a;
		int b;
	      } hier_struct;
hier_struct hier;
global_pkt local_pkt;

initial
  begin
   #10; 
   
   local_pkt.addr = 1;
   local_pkt.data = 2;
   hier.a = local_pkt;
   hier.b = 5;
   hier.a.data = 7;
   
   $display(hier.a.addr,, hier.a.data,, hier.b);
  end
endmodule


