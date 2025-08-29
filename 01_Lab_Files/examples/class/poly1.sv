class Packet ;

  task build_payld(); 
     $display("Packet payld");
  endtask

  task build_packet();
      $write("Built: ");
      build_payld();  // which task does this call?

  endtask

endclass

class DerivedPacket extends Packet ;
  Packet a = new();
   task build_payld(); // over-ridden method
     $display("DerivedPacket payld");
   endtask
 
endclass

program poly1;

DerivedPacket der = new();

initial begin
  der.build_packet();
  $finish;
  end

endprogram

