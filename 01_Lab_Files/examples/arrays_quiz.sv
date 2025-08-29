module arrays_quiz;

bit   [3:0][7:0] a;
bit              b [3:0];
bit              c [3:0][7:0];
bit        [5:0] d [3:0][31:0];
bit   [7:0][5:0] e [3:0][31:0];

initial
  begin
    $display("bit [3:0][7:0] a;\t\t",             $bits(a),, $dimensions(a),, $size(a,1),, $size(a,2));
    $display("bit            b [3:0];\t\t" ,      $bits(b),, $dimensions(b),, $size(b,1));
    $display("bit            c [3:0][7:0]; \t",   $bits(c),, $dimensions(c),, $size(c,1),, $size(c,2));
    $display("bit      [5:0] d [3:0][31:0]; \t" , $bits(d),, $dimensions(d),, $size(d,1),, $size(d,2),, $size(d,3));
    $display("bit [7:0][5:0] e [3:0][31:0];\t"  , $bits(e),, $dimensions(e),, $size(e,1),, $size(e,2),, $size(e,3),, $size(e,4));
  end

endmodule
