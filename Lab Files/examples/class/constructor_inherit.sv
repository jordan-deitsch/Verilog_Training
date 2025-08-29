module constructor_inherit();

class Packet ;
  //properties
  integer status;
  int a,b,c;
  // methods
  function new(int i);
    status = 0; 
    a = i; b = i; c = i;
 endfunction
endclass

/* fails
//-- Compiling module constructor_inherit
// Error: constructor_inherit.sv(17): Super class constructor has non-default arguments.  Arguments can be specified in the "extends" clause or by calling super.new() explicitly.
// Error: constructor_inherit.sv(17): Number of actuals and formals does not match in task call.

class DerivedPacket extends Packet ;
  //properties
  // methods
  function new();
  endfunction
 
endclass
*/

class DerivedPacket1 extends Packet ;
  //properties
  // methods
  function new(); 
    super.new(5);   
  endfunction
 
endclass

int k = 5;
class DerivedPacket2 extends Packet (k) ;
// or class DerivedPacket2 extends Packet (5) ;
  //properties
  // methods
  function new(); 
  endfunction
 
endclass



endmodule
