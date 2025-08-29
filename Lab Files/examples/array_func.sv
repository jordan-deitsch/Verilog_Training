module array_funcs;
int unsigned dyn_array[];
int assoc_array[int unsigned];
int unsigned smallest, largest, idx;
int unsigned odd[$], even[$];
int big[$], minimum[$], maximum[$];
string s[] = '{"teacher", "apple", "student"};


initial begin
//  dyn_array = new[25];
//  for (int i = 0; i < 25; i++) begin
//    dyn_array[i] = $urandom();
//    assoc_array[$urandom()] = 1;
//  end
  
  dyn_array = new[10];
  dyn_array = '{1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
  assoc_array = '{1:1, 2:2, 3:3, 4:4, 5:5, 6:6, 7:7, 8:8, 9:9, 10:10 };

  
// Note: first(), last(), next(), prev() all take a ref
//       argument and modify it.  They return a status of
//       1 or 0.
  if (!assoc_array.first(smallest))
    $display("ERROR - Assoc array has no indexes!");
    
  if (!assoc_array.last(largest))
    $display("ERROR - Assoc array has no indexes!");

  $display("Smallest index is %0d",smallest);
  $display("Largest index is %0d",largest);
  
  idx = 1;
// Note: argument to next() and prev() must already be a valid
//       index value, or function will return 0
  idx = largest;
  do 
    $display("Index %0d is set to %0d", idx, assoc_array[idx]);
  while (assoc_array.prev(idx));

    
  assoc_array = '{1:3, 2:4, 3:7, 4:6, 5:1, 6:2, 7:5, 8:10, 9:9, 10:8 };
  $display();
// Note: you can specify a undeclared placeholder name in the find() functions
//  If no name given, you can use item as a default name
  odd = assoc_array.find_index(x) with ((x % 2) != 0);
  foreach(odd[i]) $display("Index %0d is odd: %0d", odd[i], assoc_array[odd[i]]);
  
  even = assoc_array.find_index() with ((item % 2) == 0);
  foreach(even[i]) $display("Index %0d is even: %0d", even[i], assoc_array[even[i]]);

  big = assoc_array.find() with (item > 7);
  foreach(big[i]) $display("%0d > 7", big[i]);

  minimum = assoc_array.min();
  $display("Minimum is %0d", minimum[0]);
  maximum = assoc_array.max();
  $display("Maximum is %0d\n", maximum[0]);



  foreach (s[i]) $display(s[i]);
  s.reverse();
  $display("\nNow reversed: ");
  foreach (s[i]) $display(s[i]);
  s.sort();
  $display("\nNow sorted: ");
  foreach (s[i]) $display(s[i]);
end



endmodule

