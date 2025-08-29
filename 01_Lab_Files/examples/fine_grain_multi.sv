module fine_grain;

process job[1:5];

initial
 begin
   $display("Scheduling jobs 1-5" );
   for ( int j = 1; j <= 5; j++ )
     fork
       automatic int k = j;
       begin job[k] = process::self();  #k; end
     join_none

   for( int j = 1; j <= 5; j++ ) // wait for all processes to start
     wait( job[j] != null );
     
   for ( int j = 1; j <= 5; j++ )
     fork
       automatic int k = j;
       begin job[k].await(); $display("job[%0d] completed at time:%0t ns",k,$stime); end
     join_none
      
 end
  
endmodule
