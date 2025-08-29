
package alu_pkg;

  typedef enum {ADD, SUB, MUL, DIV} op_type_t;

  typedef struct {
     op_type_t mode;
     shortint unsigned val1;
     shortint unsigned val2;
     shortint unsigned result; 
     int txn_id;
  } alu_txn;

endpackage
