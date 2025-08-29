module task_ex3;

int x,y,z;  
function bit f_compare ( input int n, 
                                                   int m  ); 
    if ( n === m ) return(1); else return(0); 
endfunction 
 
function void vf_compare ( input int n, 
                                                        int m  ); 
    if ( n === m ) z = 1;  else z = 0; // global!
endfunction 

int a = f_compare( x, y );            		// n=x, m=y  implicit  
int b = f_compare( .m(5), .n(5) ); 		// n=5, m=5  explicit 
int c = f_compare( .n(3), 5 );  				// n=3, m=5  explicit 
 
initial begin 
   #10 t_compare( 8, 8, z );   				// a=1, b=8, z=c  implicit 
   #10 t_compare( .b(2), .a(4), .c(z) ); 	// a=3, b=4, z=c  explicit 
   #10 t_compare( .c(z), .a(1) );  		// a=0, b=1, z=c  explicit 
   #10 vf_compare(.n(9), 5  );   				// n=9, m=5, z=c  explicit  
end 

endmodule
