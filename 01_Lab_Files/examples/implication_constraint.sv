module implication_constraint;

typedef enum {sm, med, big} modes;

class imp_con;
  rand int unsigned z;
  modes mode;

/*  
constraint con_mode_z {
      mode == sm  -> {z < 10; z >2;}
      mode == big -> z > 50;
}
*/
///*
constraint con_mode_z {
  if (mode == sm)
   {z < 10; z > 2;}
  else if(mode == big)
   z > 50;
}
//*/
endclass

imp_con imp = new();

initial begin
  imp.mode = sm;
  for (int i=0; i <10; i++) begin
    imp.randomize();
    $display("z = %0d",imp.z);
  end
end

endmodule
