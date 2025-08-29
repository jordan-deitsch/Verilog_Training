
module enum_methods;
typedef enum {red, green, blue, yellow, white, black} colors ;
colors c = c.first();
initial begin
  forever begin
    $display("enum declaration %0d = %0s", c, c.name());
    #10;
    if(c == c.last())
      $finish;
    c = c.next();
  end
end
endmodule
