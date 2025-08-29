module forloop;


int k = 99;

initial
   for ( int j = 0, k = 10; j <= k; j++, k-- ) // j and k are local
	   #10 $display("  j: %0d  k: %0d",j,k);

initial
  #40 $display("    Global k: %0d", k);


endmodule
