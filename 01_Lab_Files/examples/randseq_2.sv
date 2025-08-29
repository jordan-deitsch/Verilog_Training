module randseq_2();

int wt = 2;
initial
  for (int i=0; i<10; i++)
    randsequence( main )
      main   : first second done;       
      first  : add := 1 | dec := wt;    
      second : pop | push ;             
      done   : { $display("done"); } ;  
      add    : { $write("add ");  } ;   
      dec    : { $write("dec ");  } ;   
      pop    : { $write("pop  "); } ;   
      push   : { $write("push "); } ;   
    endsequence
endmodule
