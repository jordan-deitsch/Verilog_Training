
module data_ex2 ();
export "DPI-C" function Double;
import "DPI-C" context task doit(input int val);

function void Double(input int num_in, output int num_out);
  num_out = 2 * num_in;
endfunction

initial
begin
  doit(2);
  doit(5);
  $finish;
end
endmodule

