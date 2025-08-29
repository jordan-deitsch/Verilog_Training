module rand_ex2;

class test;
  rand byte z;
  byte v = 10;
  
  constraint con{
    soft v > z;
  }

endclass

test U = new();

// initial
//  $monitor( U.z ,,U.v);
 
bit result;
 initial
  begin
    repeat (5)begin #10 result = U.randomize( ); $display(U.z ,,U.v,,result); end $display("..");
    repeat (5)begin #10 result = U.randomize(z); $display(U.z ,,U.v,,result); end $display("..");
    repeat (5)begin #10 result = U.randomize(v); $display(U.z ,,U.v,,result); end $display("..");
    repeat (5)begin #10 result = U.randomize() with {v < z;}; $display(U.z ,,U.v,,result); end $display("..");
    $stop;
  end


endmodule
