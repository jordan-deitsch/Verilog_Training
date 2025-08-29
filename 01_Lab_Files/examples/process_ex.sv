module process_ex;
logic[3:0] out_1, out_2;


task  automatic show_timing( input   [3:0] a, output [3:0] b );
//  input [3:0] a; output [3:0] b;
  
  #10 b = a;
  $display ($stime,,"Input: %h,  Output: %h", a,b); 

endtask


initial 
  begin
   fork
      show_timing( 4, out_1 );      // input value  4
      #5 show_timing (8, out_2);  // input value  8
   join_none
   
   wait fork;
   
  end

endmodule

