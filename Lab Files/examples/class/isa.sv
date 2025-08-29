
class Base ;
   integer status;
endclass

class Derived extends Base;
   integer fred;
endclass


module is_a;
  Base aa, bb;
  Derived cc;

  initial begin
  
    aa = new(); 
    cc = new();
    
    bb = cc;  // legal
//    bb.fred = 0;  // illegal

//    cc = bb;  // Compile time Error !
    
  end
endmodule
