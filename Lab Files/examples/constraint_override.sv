
module constraint_override;

class ex1;
  rand int unsigned a,b;

  function new;
    
  endfunction

  constraint con1 { a >10; }

endclass

class ex2 extends ex1;

  constraint con1 { a < 10; }
  constraint con2 { b < 30; }

endclass

ex1 base_handle;
ex2 derived = new();


initial begin
  base_handle = derived;
  base_handle.randomize();
  $display("a = %0d", base_handle.a);
end

endmodule

/*
output:
# Loading work.constraint_override(fast)
# run -all 
# a = 8
#  quit -f 
****************************************
*/
