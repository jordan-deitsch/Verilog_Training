// Bug Report: 
// Notice a call to a function that simply returns the
// value passed to it.
// For some reason the value is inverted on return
//
//  Verify this by re-inverting the function return value
//  as in the line commented out below

module video;

typedef struct packed{
   bit[7:0] R;
 } vid;
vid p1; 


function vid func(input vid R);
  $display("B:  R: %b", R);
  return (R);
endfunction


initial begin
  p1 = 8'd5;
  $display( "A:  R: %b ", p1.R);
  p1 = func(p1.R);
//  p1 = ~func(p1.R);
  $display( "C:  R: %b ", p1.R);
end



endmodule


/*

Compiler version 7.1_Beta2; Runtime version 7.1_Beta2;  Oct 23 12:35 2003

A:  R: 00000101
B:  R: 00000101
C:  R: 11111010
           V C S   S i m u l a t i o n   R e p o r t

*/
