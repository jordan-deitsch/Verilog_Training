module fsm_cover( input clk, rst, input_sig_1, input_sig_2,
            output reg a, b);

enum bit[1:0] { S0 = 2'h0, S1 = 2'h1, S2 = 2'h2 } state, next_state;

always @ (posedge clk)
  if (rst)  	// Fully synchronous reset
    state <= #1 S0;   
  else
    state <= #1 next_state;

always_comb begin
  case (state) 
    S0:begin
 	b = 0;
	if(input_sig_1 || input_sig_2 )
	  a = 1;
	else
	  a = 0;
	if(input_sig_1 == 1)
	  next_state = S1;
	else
	  next_state = S0;
      end
    S1:begin
	b = 1;
	a = 0;
	if(input_sig_2 == 1)
	  next_state = S2;
	else
	  next_state = S0;
      end
    S2:begin
	b = 0;
	a = 0;
	next_state = S0;
      end
    default: 
      begin
	a = 1'bx;
        b = 1'bx;
	next_state = S0;
      end
  endcase
end

covergroup cfsm  @(negedge clk);
  type_option.comment = "Coverage of FSM";
  type_option.strobe = 1;
 
    stat : coverpoint state
     {
       option.at_least = 1;
       bins valid     = {S0,S1,S2};
       bins S0_S0   = (S0 => S0);
       bins S0_S1   = (S0 => S1);
       bins S1_S0   = (S1 => S0);
       bins S1_S2   = (S1 => S2);
       bins S2_S0   = (S2 => S0);
       illegal_bins ib= {2'b11};  
       bins oops      = default ;
       bins oops_seq  = default sequence; 
     } 

endgroup

cfsm C0 = new();

endmodule

module test_fsm;
reg rst,in1,in2;
wire outa,outb;
reg clk = 0;

initial forever #100 clk = !clk;

initial begin
          rst = 0;
	  in1 = 0;
	  in2 = 0;
	  repeat(2) @(negedge clk);
	  rst = 1;
	  repeat(2) @(negedge clk);
          rst = 0;
	  repeat(2) @(negedge clk);
	  in1 = 1;
	  @(negedge clk);
	  in1 = 0;
	  in2 = 1;
	  @(negedge clk);
	  in2 = 0;
	  
	  repeat(2) @(negedge clk);
	  in1 = 1;
	  @(negedge clk);
	  in1 = 0;
	  in2 = 0;
	  @(negedge clk);
	  $stop;
        end

initial $monitor($stime,,u1.state," clk: %b ,rst: %b ,in1: %b ,in2: %b ,outa: %b ,outb: %b ",clk,rst,in1,in2,outa,outb);

fsm_cover u1(.clk(clk), .rst(rst), .input_sig_1(in1), .input_sig_2(in2), 
             .a(outa), .b(outb) );

endmodule
