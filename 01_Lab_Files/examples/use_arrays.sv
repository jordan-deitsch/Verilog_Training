module use_arrays;

bit[3:0][7:0] aa;
bit[3:0][7:0] bb [10:1];
bit[3:0][7:0] cc [10:1][3:1];


initial
  begin
    $display("\n\nPart 1:\n");
    $monitorh(bb[9],,bb[8],,bb[7]);
    bb[9] = 'hff;
    bb[8] = 'h55;
    bb[7] = 'h22;
    #100
    bb[9] = bb[8] + bb[7];
    #100    
    bb[10][1:0] = bb[9][3:2];    
    #100
    
    $display("\n\nPart 2:\n");
    $monitorh(cc[9][1]);
    #100
    cc[9][1] = 'h33221100;  // initialize 32-bit vector
    #100
    cc[9][1][3][7] = 1'b1;  // set MSB of MSbyte of 32-bit vector
    #100 			
    cc[9][1][3] = 8'haa;    // load MSbyte of 32-bit vector
    #100; 			
    $display("\n\n");
  end



/* Simulator Transcript

Part 1:

000000ff 00000055 00000022
00000077 00000055 00000022


Part 2:

00000000
33221100
aa221100

*/




endmodule
