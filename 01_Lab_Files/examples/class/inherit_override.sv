
module inherit_override();

class Packet ;
  //properties
  int status = 4;

  function void setstat(int s);
    status=s;
    $display ("Parent setstat");
  endfunction
endclass

class DerivedPacket extends Packet ;

  function void setstat(int s);
    status=s;
    $display ("child setstat");
  endfunction
endclass

DerivedPacket p = new();

initial begin
  p.status = 44;  //OK can access inherited property
  p.setstat(33);   // output is "child setstat"
end


endmodule
