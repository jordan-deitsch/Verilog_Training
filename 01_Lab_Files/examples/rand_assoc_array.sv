module rand_assoc_array;


class a_array;
  rand bit [2:0] d_a[bit[3:0]];
  constraint a_size {d_a.num() >8;  d_a.num() < 12;  }
endclass

a_array assoc_array = new();
bit rand_result;

initial begin
  assoc_array.a_size.constraint_mode(0);  // turn off constraint
  $display("without constraining size of array: \n");
  for (int i = 1; i<=3; i++) begin
    assoc_array.d_a[i] = i;
    $display("size of assoc_array before randomization = %d", assoc_array.d_a.num());
    rand_result = assoc_array.randomize();
    $display("size of assoc_array after  randomization = %d \n", assoc_array.d_a.num());
  end
  $display("\n with constraining size of array: \n");
  assoc_array.a_size.constraint_mode(1);  // turn on constraint
  for (int i = 1; i<=3; i++) begin
    assoc_array.d_a[i] = i;
    $display("size of assoc_array before randomization = %d", assoc_array.d_a.num());
    rand_result = assoc_array.randomize();
    $display("size of assoc_array after  randomization = %d \n", assoc_array.d_a.num());
  end
end

endmodule
