virtual class Display;
integer v;

  virtual task Print(); 
     $display("v (dec) : ",v);
  endtask

endclass

class HexDisplay extends Display ;  

   task Print(); // over-ridden method
     $displayh("v (hex) : ",v);
   endtask
 
endclass

class OctDisplay extends Display ;  

   task Print(); // over-ridden method
     $displayo("v (oct) : ",v);
   endtask
 
endclass

class BinDisplay extends Display ;  

   task Print(); // over-ridden method
     $displayb("v (bin) : ",v);
   endtask
 
endclass

program poly5;

HexDisplay hx = new();
OctDisplay oc = new();
BinDisplay bn = new();
Display poly;

initial begin
  hx.v = 'b1010_1011_1100_1101;
  oc.v = 'b1010_1011_1100_1101;
  bn.v = 'b1010_1011_1100_1101;

  $display("\n\n");
  
  poly = hx;
  poly.Print();

  poly = oc;
  poly.Print();

  poly = bn;
  poly.Print();

  $display("\n\n\n");
  
  $finish;
  end

endprogram

