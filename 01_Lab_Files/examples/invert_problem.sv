module video;
 typedef struct packed{
   bit[7:0] R,X,G,B;
 } vid;
vid p1; 


function vid invertPixel2(input bit[7:0] R,X,G,B);
vid t;
  $display("TWO:  R: %0d  G:%0d  B:%0d", R,X,G,B);
  t = {R,X,G,B};
  $display("THREE:  R: %0d  X:%0d  G:%0d  B:%0d", t.R,t.X,t.G,t.B);
  return (t);
endfunction


initial begin
  p1 = {8'd10,8'd20,8'd30,8'd40};

  $display( "ONE:  R: %0d  X: %0d  G:%0d  B:%0d", p1.R,p1.X,p1.G,p1.B);

  p1 = invertPixel2(p1.R,p1.X,p1.G,p1.B);

  $display( "FOUR:  R: %0d  G:%0d  B:%0d", p1.R,p1.X,p1.G,p1.B);
end



endmodule


/*
Compiler version 7.1_Beta1; Runtime version 7.1_Beta1;  Oct 22 16:31 2003


I0:  R: 10  G:30  B:40
CP0  R: 10  G:30  B:40
CP1  R: 0  G:10  B:215
I1:  R: 255  G:245  B:40
          V C S   S i m u l a t i o n   R e p o r t


*/
