module randseq_3();
int wt = 2;
bit[1:0] status = 0;
bit up = 0;
initial
  for (int i=0; i<10; i++) begin
    status++;
    up++;
    randsequence( main )
      main:  first second third;        
      first: case (status)              
                0,1:  done;             
                2:    third;             
                default: illeg;         
             endcase ;                  
      second: add := 1 | dec := wt;      
      third:if (up) pop else push ;    

      done : { $display("done"); } ;    
      add  : { $write("add ");  } ;     
      dec  : { $write("dec ");  } ;     
      pop  : { $write("pop  "); } ;     
      push : { $write("push "); } ;     
      illeg: { $display("Illegal Status"); } ;
    endsequence
  end
endmodule
