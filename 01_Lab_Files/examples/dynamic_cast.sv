class Packet ;
  	  integer status;
endclass

class Pkt  extends Packet;
   integer fred;
endclass

module same_class;
  Packet aa, bb;

  initial begin
    aa = new(); bb = new();
    if ( $cast (aa, bb) )	// returns 1
      $display("Objects are of compatible type");
   else
      $display("Should never see this");
  end
endmodule

module base2derived;
  Packet aa, bb;
  Pkt cc;

  initial begin
    aa = new(); cc = new();
    if (!( $cast(cc, aa) ))	 // returns 0
      $display("Illegal cast - from base to derived");

    if ( $cast(aa,cc) )	 // returns 1
      $display("Legal -  derived to base ");

    if ( $cast(cc, aa) )	 // returns 1
      $display("Now a legal cast - back to derived");

 // cc = aa; // But this will ALWAYS give a compile error
  end
endmodule

module is_a;
  Packet aa, bb;
  Pkt cc;

  initial begin
  
    aa = new(); 
    cc = new();
    
    bb = cc;  // legal

//    cc = aa;  // Compile time Error !
    
  end
endmodule
