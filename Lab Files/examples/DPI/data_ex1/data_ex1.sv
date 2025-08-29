module data_ex1 ();
import "DPI-C" context function void print_logic ( input logic logic_in );

logic A = 0;

initial
begin
  print_logic(A);
  A = 1;
  print_logic(A);
  A = 1'bX;
  print_logic(A);
  A = 1'bZ;
  print_logic(A);
  $finish;
end
endmodule

