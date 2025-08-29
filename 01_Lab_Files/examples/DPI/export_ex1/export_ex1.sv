module export_ex1();
  export "DPI-C" function SVrand;
  export "DPI-C" task init_rand;
  import "DPI-C" context task my_C_task();

  task init_rand();
    $display("Desired seed: 12345");
  endtask

  function int SVrand();
    return $urandom();
  endfunction

  initial begin
    my_C_task();
    $finish();
  end

endmodule


