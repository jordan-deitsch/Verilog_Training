module cover_ex;

event smpl;

class cpoints;

  rand bit [7:0] a;
  bit expr = 1;
  bit  ok = 1;
  int arg = 60;

  covergroup cg_a (ref bit[7:0] target, input int val,  bit gat) @(smpl);
     cp_a : coverpoint a iff ( gat )
   {
     bins val_bin[] = { [val:val+5] }; // i.e. 60:65
   }
  endgroup

  function new();
    // Instantiate and pass in arguments to covergroup
    cg_a = new(.target(a), .val(arg), .gat(expr));
  endfunction

endclass

cpoints cp;

initial begin
  cp = new();
  for (int i=0; i<50; i++) begin
    void'(cp.randomize() with { a inside {[60:70]}; } );
    -> smpl;
    $display("%0d coverage = ", i, cp.cg_a.get_coverage() );
  end
end

endmodule
