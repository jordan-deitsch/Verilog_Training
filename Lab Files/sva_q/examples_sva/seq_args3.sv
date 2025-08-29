
module seq_args;

logic [7:0] a = 0;
logic [7:0] data_bus = 0;
logic [0:3] c_be;
logic [0:3] b;
bit clk = 0;
bit w = 0,
    x = 0,
    y = 0,
    z = 0;

always #20 clk = !clk;

initial
  begin
    #40 w = 1; x = 1;
    #40 w = 0; x = 0; y = 1;
    #40 y = 0; z = 1;
    #40 z = 0;
    
   #80 $stop;
    
  end

sequence seq_w_local ( check, delay );
    y == check ##delay z == check;
endsequence

parameter my_delay = 1;

property p1;
  bit loc;
  @(posedge clk) ($rose(w), loc = x) |=> seq_w_local ( loc, my_delay );
endproperty


p_example1 : assert property ( p1 );


endmodule
