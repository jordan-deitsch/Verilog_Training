class Packet ;
integer ID = 5;
  virtual task build_payld(); 
  //   $display("ID: %d  Packet payld", ID);
  endtask

  task build_packet();
      $write("Built: ");
      build_payld();  // which task does this call?

  endtask

endclass

class DerivedPacket extends Packet ;
//integer ID = 6;  
   task build_payld(); // over-ridden method
     $display("ID: %d DerivedPacket payld",ID);
   endtask
 
endclass

program poly4;

DerivedPacket der = new();

initial begin
  der.build_packet();
  $finish;
  end

endprogram

