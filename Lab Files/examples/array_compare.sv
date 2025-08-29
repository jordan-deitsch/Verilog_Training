module array_compare;

int a[] = new[8];
int b[] = new[6];

initial begin
  for (int i=0; i<a.size(); i++) a[i] = i;
  for (int i=0; i<b.size(); i++) b[i] = i;
  if(a == b)
    $display("same");
  else
    $display("different");
end
  
endmodule
