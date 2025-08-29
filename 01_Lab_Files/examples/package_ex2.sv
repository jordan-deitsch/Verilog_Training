
package p;
  typedef enum { FALSE, TRUE } BOOL;
  const BOOL c = FALSE;
endpackage

package q;
  const int c = 0;
endpackage


module foo2;
  import q::*;
  wire a = c;  // This statement equivalent to wire a=q::c;
  import p::c; // The conflict with q::c and p::c creates an error.
  
 
endmodule

module foo;
  wire a = q::c;  // fully resolved reference to c in package q
endmodule
  
