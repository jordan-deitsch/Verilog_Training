module constraint_1;

bit [31:0] f;

class ex2;
  rand int a,b,c,d,e;

  constraint con_ab { a > b; a < 256; (a - b) >= 64; }
 
  constraint con_c { c inside { [1:5], 12, [(a-b):(a+b)] }; }

  integer primes[0:4] = '{2,3,5,7,11}; 
  constraint con_d { d inside {primes};  }

  function automatic int  count_ones ( bit [31:0] w );
     for( count_ones = 0; w != 0; w = w >> 1 )
          count_ones += w & 1;
  endfunction

  constraint con_ef { e == count_ones( f ) ; }

endclass
endmodule
