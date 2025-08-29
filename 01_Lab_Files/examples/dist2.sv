class test_dist;
rand int x;

constraint con_x {
      x dist { [1:4] :/ 2 , 5 := 3 , 6 := 4, 7 };
}
endclass

module dist2;
test_dist td = new();
bit rr;
int result[9];
initial begin
 for (int i=0; i<1000; i++) begin
   rr = td.randomize();
   result[td.x]++;  
 end
 for (int i=1; i<8; i++)
   $display("%0d count = %0d",i,result[i]);
end
endmodule
