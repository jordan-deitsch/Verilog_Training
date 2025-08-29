module ref_arg();

function automatic int crc( ref byte packet [1000:1] );
  for( int j= 1; j <= 1000; j++ ) begin
    crc ^= packet[j];
  end
endfunction

byte byte_array[1000:1];

initial begin
  for (int i=1; i<= 1000; i++)
    byte_array[i] = i;  //init array
  $display (crc(byte_array) );
end  
endmodule
