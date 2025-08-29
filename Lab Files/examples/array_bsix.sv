module array_bsix;

typedef bit[1:6] bsix;     // 6-bit packed vector
bsix [1:10] minea;         // 60-bit packed vector
bit[1:10][1:6] mineb;
bit[1:60] minec;
bit [7:0] nna [0:5];       // unpacked array of 6 bytes
bit [7:0] nnb [5];         // unpacked array of 6 bytes 

initial begin
  $display( $right(minea,1),$right(minea,2) );
  $display( $right(mineb,1),$right(mineb,2) );
  $display( $right(nna,1),$right(nnb,1) );
  $display( $size(nna,1),$size(nnb,1) );
  end

endmodule
