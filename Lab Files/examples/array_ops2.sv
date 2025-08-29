module array_ops2;
int var=3;
bit[7:0] PA = 8'haa, PB = 8'hbb;

byte UA [7:0] = {default: 'haa};
byte UB [7:0] = {default: 'hbb};

bit[3:0][7:0] MPA;
initial
 begin
   $monitor($stime,,"PA: %h, PB: %h, UA[4]: %h, UB[4]: %h",PA,PB,UA[4],UB[4]);
   #10 PA = PB;
       UA = UB;
   
   #10 PA[7:4] = 'hA;
       PB[3:0] = PA[7:4];
       UA[4][7:4] = 'hA;    
       UB[4][3:0] = UA[4][7:4];
       
   #10 PA[var -:4] = PA[var+1 +:4];
       UA[4][var -:4] = UA[4][var+1 +:4];  
       
   #10 $monitor($stime,,"MPA: %h",MPA);
   
   #10 MPA = 32'hdeadbeef; 
   #10 MPA = MPA+1;      
 end
 
/* 
Compiler version 7.1_Beta2; Runtime version 7.1_Beta2;  Oct 28 10:36 2003

         0 PA: aa, PB: bb, UA[4]: aa, UB[4]: bb
        10 PA: bb, PB: bb, UA[4]: bb, UB[4]: bb
        20 PA: ab, PB: ba, UA[4]: ab, UB[4]: ba
        30 PA: aa, PB: ba, UA[4]: aa, UB[4]: ba
        40 MPA: 00000000
        50 MPA: deadbeef
        60 MPA: deadbef0
           V C S   S i m u l a t i o n   R e p o r t
Time: 50
*/





endmodule
