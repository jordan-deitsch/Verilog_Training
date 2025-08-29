logic [7:0] a = 0;
event global_event;
module test;

initial
  begin
     $monitor("%t: a =%d, U1.a =%d",$time,a,U1.a);
     #20;
     -> global_event;
  end


local1 U1();

endmodule

module local1;
logic [7:0] a;

always @($root.global_event)
  begin
    $display($stime,"    global_event detected in: %m");
    a = 1;
  end  
    
local2 U2();
    
endmodule

module local2;

always @($root.global_event)
  begin
    $display($stime,"    global_event detected in: %m");
    #20;
    $root.a = 2; 		// assign $root.a
    #20;
    U1.a = 2; 		// assign U1.a
    #20
    $root.a = 4;	// assign $root.a
  end
    
endmodule

// Logfile
//  0: a =  0, U1.a =  x
//     global_event detected in: $root.U1.U2
//     global_event detected in: $root.U1
// 20: a =  0, U1.a =  1
// 40: a =  2, U1.a =  1
// 60: a =  2, U1.a =  2
// 80: a =  4, U1.a =  2
