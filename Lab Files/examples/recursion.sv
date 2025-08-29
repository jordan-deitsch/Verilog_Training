module recursion;
int a,n;
bit go;

factorial F1 (.*);

initial
  begin
    $monitor($stime,,a);
    go = 0; n = 0;
    #10 n = 5;
        go = 1;
    #10 go = 0;	
    #10 n = 6;
        go = 1;
    #10 $stop;
  end  
  
endmodule  
