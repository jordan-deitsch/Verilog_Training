class test_dist;
rand int x;
int c = 1;

constraint con_x {
      x dist { [1:2] := c , 3 := 3 , 4 := 5 };
}
endclass

module dist1;
test_dist td = new();
bit rr;
int result[6];
initial begin
 for (int i=0; i<1000; i++) begin
   rr = td.randomize();
   result[td.x]++;  
 end
 for (int i=1; i<5; i++)
   $display("%0d count = %0d",i,result[i]);
end
endmodule
