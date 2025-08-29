module import_ex1();
  int num;
  import "DPI-C" task init_rand();
  import "DPI-C" function int Crand();
  initial
  begin
    init_rand();
    num = Crand();
    $display( num );
    $finish();
  end
endmodule

