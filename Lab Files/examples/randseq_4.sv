module randseq_4();
int status;
initial
  for (int i=0; i<10; i++) begin
    status = i;
    randsequence( main )
      main  : first second third;            
      first : add := 1 | dec := 2;            
      second: { if (status == 2)
                    begin $write("RETURN "); return;
                    end } pop | push; 
      third : { if (status == 3)
                    begin $display("BREAK" ); break; 
                    end} done  ;
      done  : { $display("done"); } ;           
      add   : { $write("add ");  } ;            
      dec   : { $write("dec ");  } ;            
      pop   : { $write("pop  "); } ;            
      push  : { $write("push "); } ;            
    endsequence
end
endmodule
