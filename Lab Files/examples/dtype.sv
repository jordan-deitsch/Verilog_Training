module dtype;

reg a;
logic b, c, d;

//assign a = c;
assign b = c;  // logic assigned continuously
and (d,b,a);   // logic driven by prim. output

initial 
  begin
    $monitor ("d: %b,c: %b, a: %b, b: %b", d,c,a,b);
    c = 0;     // logic assigned procedurally
    a = 1;
    #1 c = 1;
    #1 c = 2;
    #1 c = 0;
  end



endmodule
