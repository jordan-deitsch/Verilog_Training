module test;
string abc;

initial
  begin
    abc = "def";
    abc[0:1] = "pu";
    $display(abc);
  end



endmodule
