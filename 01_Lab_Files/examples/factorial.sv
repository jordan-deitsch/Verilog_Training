module factorial(input bit go,
                 input int n,
                 output int a);


function automatic int factorial (int n);
  if(n==0) return(1);
  else return(factorial(n-1)*n);
endfunction


always @(posedge go)
    a = factorial(n);
  
endmodule 
