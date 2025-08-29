
module cover_illegal();
event smpl;

class check_illegal;
rand bit [7:0] a;
bit expr = 1;
bit ok = 0;

covergroup cg_a @(smpl);
  cp_a : coverpoint a iff ( expr ) 
     {
	bins some_range = { [0:67] };
        bins chk_66 = {66};      
	ignore_bins ib67 = { 67 };
        illegal_bins ib_66 = { 66 };
        illegal_bins ib3 = ( 5 => 6 ) iff !ok;
	bins oops_val  = default;
        bins oops_seq = default sequence;
      } 
endgroup

function new();
  cg_a = new();
endfunction

endclass

check_illegal ci = new();


initial begin
  for (int i = 0; i<256; i++) begin
    #1 ci.a = i;
  
//  for (int i=0; i<1000; i++) begin
//    void'(ci.randomize());
    -> smpl;
  end
  $stop();
end
endmodule
