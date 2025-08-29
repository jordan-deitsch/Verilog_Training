module cast;
reg [7:0] a ,b;
typedef int mytype;
mytype green;

initial
  begin
    a = 254; b = 1;
    $display(int' (2.0*3.0));   	// Cast result to integer
    $displayb(10' (a+b));		   // implies a number of bits (10 here) 
    $displayb(signed' (a));		// works for sign-changing too
    
    green = mytype' (b);		
    $display(green);
  end
  
endmodule  
