module enum_ex;

typedef enum  {b1=1,b2,b3,b4,b5,b6,b7,b8} byte_lane; 
bit [8:1][7:0] bus;

    initial
      begin
        $monitorh(bus);
	bus = 'b0;
	#10
        bus[b1] = 'haa;	// load LS Byte
	#10
        bus[b8] = 'hbb;	// load MS Byte
	#10;
      end

endmodule
