
module seq_args;

logic [7:0] a = 0;
logic [7:0] data_bus = 0;
logic [0:3] c_be;
logic [0:3] b;
bit clk = 0;
bit x = 0,
    y = 0,
    z = 0;

always #20 clk = !clk;

initial
  begin
    #40 x = 1;
    #40 x = 0; y = 1;
    #40;
    #40 y = 0; z = 1;
    #40 z = 0;
    
    #80 x = 1;
    #40 x = 0; y = 1;
    #80;
    #80;
    #40 y = 0; z = 1;
    #40 z = 0;
    #80 $stop;
    
  end

sequence seq_w_delay ( rep = 2, shortint delay1 = 1 );
   x ##delay1 y[*rep] ##delay1 z;
endsequence


parameter my_delay = 2;

p_example1 : assert property ( @(posedge clk)
				$rose(x) |-> seq_w_delay ( ));
p_example2 : assert property ( @(posedge clk)
 				$rose(x) |-> seq_w_delay ( 3, my_delay ));


endmodule
