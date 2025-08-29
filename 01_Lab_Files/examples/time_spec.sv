module timespec;
timeunit 1ns;		
timeprecision 0.1ns;	 // time accuracy local to this module !

initial
  begin
   #5.19  $display("Current time is %f",  $realtime);
  end
    
endmodule
