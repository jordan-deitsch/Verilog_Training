module task_ex4;

bit[7:0] dat; 


task automatic show ( const ref bit[7:0] data );
   for ( int j = 7; j >= 0 ; j-- )
         #10 $display( data[j] ); 
   data = 5;	 
endtask


initial
  begin
    $monitor("dat = %b",dat);
    dat = 8'b10000000;
    fork
      show(dat);
      #40 dat = 8'b10000001;
    join
    #100 $finish;  
  end

endmodule
