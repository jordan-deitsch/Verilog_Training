module rand_ex;

class test;
  rand int z;
  
  int mode;
  
  constraint con_mode_z{
    mode == 0  -> { z<10; z>2; }
    mode == 1 -> z>50;
  }

endclass

test U = new();
  initial
  begin
    U.mode = 0;
    #100 U.mode = 1;
    #100 U.mode = 0;
    #100 $stop;
  end

  initial
  begin
    repeat(50) begin
      #5 U.randomize();
      $display(U.z);
      end
  end


endmodule
