
module rand_case();

int results[3];
int w = 3;

initial begin
  for(int i=0; i<1000; i++)
    randcase
       1: results[0]++;
       w: results[1]++;
       6: results[2]++;
    endcase
  for (int i=0; i<3; i++)
   $display("%0d count = %0d",i,results[i]);
end
endmodule
