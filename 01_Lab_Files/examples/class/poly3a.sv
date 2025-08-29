class Packet ;

  virtual task build_payld(); 
     $display("Packet payld");
  endtask

  task build_packet();
      $write("Built: ");
      build_payld();  // which task does this call?

  endtask

endclass

class DerivedPacket extends Packet ;
  
   task build_payld(); // over-ridden method
     $display("DerivedPacket payld");
   endtask
 
endclass

class DDPacket extends Packet ;
  
   task build_payld(); // over-ridden method
     $display("DDPacket payld");
   endtask
 
endclass

program poly3a;

DerivedPacket der = new();
Packet p = der;

initial begin
  p.build_packet();
  $finish;
  end

endprogram

