module array_ops3;
//int var = 3;
bit[7:0] PA [3:0];
bit[1:0][7:0] PB [3:0];

byte UA [7:0];// = {default: 'haa};
byte UB [7:0][1:0];// = {default: 'hbb};

initial
 begin
   #10 $readmemh("hex.dat",PA);
       for(int i=0; i<=3;i++) $display("PA[%0h",i,"]: %b",PA[i]);
   #10 $readmemh("hex.dat",PB); $display("");
       for(int i=0; i<=3;i++) $display("PB[%0h",i,"]: %b",PB[i]);
   #10 $readmemh("hex.dat",UA); $display("");   
       for(int i=0; i<=3;i++) $display("UA[%0h",i,"]: %b",UA[i]);
   #10 $readmemh("hex_multi.dat",UB); $display("");   
       for(int i=0; i<=3;i++) 
         for(int j=0; j<=1;j++) 
           $displayh("UB[",i,"][",j,"]: ",UB[i][j]); 
 end
 
/* 
// EXPECTED SIMULATOR OUTPUT

PA[0]: 00000000
PA[1]: 00000001
PA[2]: 10101010
PA[3]: 11111111

PB[0]: 0000000000000000
PB[1]: 0000000000000001
PB[2]: 0000000010101010
PB[3]: 0000000011111111

UA[0]: 00000000
UA[1]: 00000001
UA[2]: 10101010
UA[3]: 11111111

UB[00000000][00000000]: 00
UB[00000000][00000001]: 01
UB[00000001][00000000]: 10
UB[00000001][00000001]: 11
UB[00000002][00000000]: 20
UB[00000002][00000001]: 21
UB[00000003][00000000]: 30
UB[00000003][00000001]: 31

Time: 30
*/





endmodule
