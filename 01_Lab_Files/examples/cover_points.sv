module cover_points;

event smpl;

class cpoints;

rand bit [7:0] a;
bit expr = 1;
bit  ok = 1;
covergroup cg_a @(smpl);
   cp_a : coverpoint a iff ( expr )
 {
   bins arange      = { [0:63] };
   bins vals        = { 64, [67:127] };

   bins mid_a[ ]    = { [128:147] };
   bins distr[10]   = { [149:169] };

//   wildcard bins wb = {8b0101zx?1};

   bins seq         = ( 255 => 0, 0 => 99);
 bins upper       = { [150:$] } iff (ok) ;
 }
endgroup

function new();
  cg_a = new();
endfunction

endclass

cpoints cp;

initial begin
  cp = new();
  for (int i=0; i<10; i++) begin
//    cp = new();
    void'(cp.randomize());
    -> smpl;
    $display("coverage = ",cp.cg_a.get_coverage());
  end
end

endmodule
