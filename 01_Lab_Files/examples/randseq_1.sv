module randseq_1();

initial
  for (int i=0; i<10; i++)
    randsequence( main )
      main   : first second done;       
      first  : add | dec  ;             
      second : pop | push ;             
      done   : { $display("done"); } ;  
      add    : { $write("add ");  } ;   
      dec    : { $write("dec ");  } ;   
      pop    : { $write("pop  "); } ;   
      push   : { $write("push "); } ;   
    endsequence
endmodule
