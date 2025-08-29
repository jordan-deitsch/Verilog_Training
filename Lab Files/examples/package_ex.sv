
package p;
   typedef enum { FALSE, TRUE } BOOL;
   const BOOL c = FALSE;
endpackage

package q;
   const int c = 0;
endpackage

module foo;
   import q::*;
   wire a = c;  // This statement forces the import of q::c;
   import p::c; // The conflict with q::c and p::c creates an error.
endmodule





