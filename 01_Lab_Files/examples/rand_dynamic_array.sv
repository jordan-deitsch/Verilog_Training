
module rand_dynamic_array;

class d_array;
  rand bit [3:0] d_a[];
  constraint a_size {d_a.size() >8;  d_a.size() < 12;  }
endclass

d_array dyn_array = new();
bit rand_result;

initial begin
  dyn_array.a_size.constraint_mode(0);  // turn off constraint
  $display("without constraining size of array: \n");
  for (int i = 1; i<=3; i++) begin
    dyn_array.d_a = new[i];
    $display("size of dyn_array before randomization = %d", dyn_array.d_a.size());
    rand_result = dyn_array.randomize();
    $display("size of dyn_array after  randomization = %d \n", dyn_array.d_a.size());
  end
  $display("\n with constraining size of array: \n");
  dyn_array.a_size.constraint_mode(1);  // turn on constraint
  for (int i = 1; i<=3; i++) begin
    dyn_array.d_a = new[i];
    $display("size of dyn_array before randomization = %d", dyn_array.d_a.size());
    rand_result = dyn_array.randomize();
    $display("size of dyn_array after  randomization = %d \n", dyn_array.d_a.size());
  end
end

endmodule
