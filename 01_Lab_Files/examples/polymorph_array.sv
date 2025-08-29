

module test;

class base_class;
  int a = 3;
  virtual function void print_type();
    $display("I am a base_class");
  endfunction
endclass

class sub_class_a extends base_class;
  int a = 1;
  function void print_type();
    $display("I am a sub_class_a");
  endfunction
endclass
  int abc[] = new[8];
  base_class bc_array[] = new[5];
  sub_class_a dc = new();
  
  initial begin
    bc_array[0] = dc;
    bc_array[0].print_type();
    $display(bc_array[0].a);
  end
endmodule
