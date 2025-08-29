module pu_bytex;
bit [63:0] bus;
typedef enum {b1=1,b2,b3,b4,b5,b6,b7,b8} byte_lane;
typedef union packed { bit     [63:0] bus;
		       bit [8:1][7:0] b;
		     } bex;

function bit[7:0] bytext(input bit[63:0] bb, byte_lane lane);
 bex a;
 a.bus = bb;
 return a.b[lane]; 
endfunction


initial
begin
  bus = 64'haabbccddeeff0011;
  for(int i=8; i>0; i--)
    $displayh(bytext(bus,i));
end


endmodule

