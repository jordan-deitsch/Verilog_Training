module test;

class packet;
rand  int unsigned array[10];
// randc cannot be used in combination with unique on an array
//randc  int unsigned array[10]; // causes array[i] to not repeat

function void print();
  $write("array: ");
  foreach (array[i]) $write("%0d, ",array[i]);
  $display();
endfunction

int  primes[] = '{2,3,5,7,11,13,17,19,23,29};
//constraint bad1 {unique { 0,1,2,3,4,5,6,7,8,9 };}  // only variables allowed, no constants
//constraint bad2 { foreach (array[i]) array[i] inside {0,1,2,3,4,5,6,7,8};} // too few values for uniqueness
//constraint uniq {unique { array };}
//constraint values { foreach (array[i]) array[i] < 10;}
//constraint values { foreach (array[i]) array[i] inside {0,1,2,3,4,5,6,7,8,9};}
constraint values { foreach (array[i]) array[i] inside {primes};}
//constraint values { foreach (array[i]) array[i] dist { [0:9]:=20 , [10:19]:=1 };}
endclass

packet pkt = new;

initial begin
  repeat(10)
    begin
      void'(pkt.randomize());
      pkt.print();
    end
end



endmodule
