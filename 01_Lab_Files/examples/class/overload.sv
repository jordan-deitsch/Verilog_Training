
module overload;

class base;
  int a;
  function void init(int a_arg);
    a = a_arg;
  endfunction

endclass

class derived extends base;
  string b;

  function void init(int a_arg,
                     string b_arg
                    );
    super.init(a_arg);
    b = b_arg;
  endfunction

endclass

initial begin
  derived d = new();
  d.init(5, "this works!");
  $display("a = %0d, b = %s", d.a, d.b);
end

endmodule // overload