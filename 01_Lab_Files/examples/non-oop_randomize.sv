module stim;
class stimc;
   rand bit [15:0] addr;
   rand bit [31:0] data;
   rand bit rd_wr;
   constraint c { addr < 1024; }
endclass


function bit gen_stim_oop( stimc p );
  bit success;
  success = p.randomize();
  return p.rd_wr;
endfunction

   bit [15:0] addr;
   bit [31:0] data;
   bit rd_wr;

function bit gen_stim();
   bit success;
   success = randomize( addr, data, rd_wr ) with { addr < 1024 ; }; 
   return (rd_wr) ;
endfunction

stimc sc = new();
initial begin
  for (int i=0; i<10; i++) begin
   $display("non-oop: rd_wr = %b", gen_stim());
   $display("oop:     rd_wr = %b", gen_stim_oop(sc));
  end
end

endmodule
