
class static_ex;
  static integer fileId = $fopen( "data", "r" );
  static int val;
  static function void print_val();
    $display("val = %0d", val);
  endfunction
endclass

program test;
static_ex s1;  //Only handle is required
static_ex s2;
bit[7:0] c;
initial begin
 c = $fgetc( s1.fileId );
 $display("%0s", c);
 s1.val = 22;
 s1.print_val();
 s2.val = 44;
 s1.print_val();
end
endprogram
