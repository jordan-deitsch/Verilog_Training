typedef enum [1:0] { S0 = 2'h0, S1 = 2'h1, S2 = 2'h2 } states;

module test_sm_ex;
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

initial $monitor($stime,,u1.state," clk,rst: %b ,in1: %b ,in2: %b ,outa: %b ,outb: %b ",clk,rst,in1,in2,outa,outb);


imm_assert_ex u1(.clk(clk), .rst(rst), .input_sig_1(in1), .input_sig_2(in2), 
             .a(outa), .b(outb) );


endmodule

module imm_assert_ex( input wire  clk, rst, input_sig_1, input_sig_2, 
             output reg   a, b);

`define TRUE 1
`define FALSE 0

states state, next_state;
time t;

always @ (posedge clk)
  if (rst)  	// Fully synchronous reset
    state <= #1 S0;   
  else
    state <= #1 next_state;

always @*  // sensitive to state and all inputs
  begin
    case (state) 
      S0:  
        begin
 	  b = `FALSE;
	  if(input_sig_1 || input_sig_2 )
	    a = `TRUE;
	  else
	    a = `FALSE;
	  if(input_sig_1 == `TRUE)
	    next_state = S1;
	  else
	    next_state = S0;
        end
      S1: 
        begin
	  b = `TRUE;
	  a = `FALSE;
	  if(input_sig_2 == `TRUE)
	    next_state = S2;
	  else
	    next_state = S0;
        end
      S2:
        begin
	  b = `FALSE;
	  a = `FALSE;
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

always @(negedge clk)
  if (state == S2)
    S2_assert: assert (a && !b) $fatal("OK"); // DELIB. ERROR should be !a
                      else begin
		             t = $stime;
			      $display("%m failed at time %0t", t);
			   end  
			     
			     
			     
endmodule
