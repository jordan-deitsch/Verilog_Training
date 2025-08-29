module simple_cross;
event smpl;

class scross;
  typedef enum {a,e,i,o,u} vowels;
  rand vowels v;
  bit inactive = 1;
  rand bit[2:0] cnt;

  covergroup cg @(smpl);
      a: cross cnt, v iff (inactive);   
  endgroup

  function new();
    cg = new();
  endfunction
endclass

scross sc = new();

initial
  for (int i=0; i<100; i++) begin
    void'(sc.randomize());
    -> smpl;
  end

endmodule
