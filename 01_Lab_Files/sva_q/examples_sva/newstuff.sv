module testNewStuff;

wire a,b,c, clk, rst, done;


property p3; 
  b ##1 c; 
endproperty

c1: cover property (@(posedge clk) a #-# p3); 
a1: assert property (@(posedge clk) a |-> p3);

// FOLLOWED-BY
property p1;
##[0:5] done #-# always !rst;
endproperty
property p2;
##[0:5] done #=# always !rst;
endproperty

// NEXTTIME
// if the clock ticks once more, then a shall be true at the next clock tick 
property p1a;
  nexttime a; 
endproperty

// the clock shall tick once more and a shall be true at the next clock tick. 
property p2a;
  s_nexttime a; 
endproperty

// as long as the clock ticks, a shall be true at each future clock tick 
// starting from the next clock tick
property p3a;
  nexttime always a; 
endproperty

// the clock shall tick at least once more and as long as it ticks, a shall 
// be true at every clock tick starting from the next one
property p4;
  s_nexttime always a; 
endproperty

// if the clock ticks at least once more, it shall tick enough times for a to 
// be true at some point in the future starting from the next clock tick 
property p5;
  nexttime s_eventually a; 
endproperty

// a shall be true sometime in the strict future 
property p6;
  s_nexttime s_eventually a; 
endproperty

// if there are at least two more clock ticks, a shall be true at the second 
// future clock tick
property p7;
  nexttime[2] a; 
endproperty

// there shall be at least two more clock ticks, and a shall be true at the 
// second future clock tick
property p8;
  s_nexttime[2] a; 
endproperty

// ALWAYS

initial a1a: assume property( @(posedge clk) rst[*5] #=# always !rst);

property p11;
  a ##1 b |=> always c;
endproperty

property p21; 
  always [2:5] a;
endproperty

property p31; 
  s_always [2:5] a;
endproperty

property p41; 
  always [2:$] a;
endproperty





/*  // UNTIL
property p1b; 
  a until b;
endproperty

property p2b;
  a s_until b;
endproperty

property p3b;
  a until_with b;
endproperty
*/

// EVENTUALLY
property p4b; 
  eventually [2:5] a;
endproperty

property p5b; 
  s_eventually [2:5] a;
endproperty

//property p6b;
//  eventually [2:$] a; // Illegal
//endproperty

property p7b; 
  s_eventually [2:$] a;
endproperty





endmodule
