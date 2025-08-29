class Packet ;
   integer status;
endclass

program same_class;
  Packet aa, bb;


  initial begin
    aa = new(); bb = new();
    if ( $cast(aa, bb) )	// returns 1
      $display("Objects are of compatible type");
    else
      $display("Objects are of incompatible type");
  end
endprogram


class Pkt  extends Packet;
   integer fred;
endclass

program base2derived;
  Packet aa, cc;
  Pkt bb;

  initial begin
    aa = new(); bb = new(); cc = bb;
    if ( $cast(bb, aa) )	 // returns 0
      $display("Should never see this");
    else
      $display("Illegal cast - from base to derived");

    if ( $cast(cc, aa) )	 // returns 1
      $display("Legal - uses base handle to derived object");
    else
      $display("Should never see this");
  end
endprogram

