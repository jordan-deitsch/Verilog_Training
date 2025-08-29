
class alu_txn;
  op_type_t mode;
  shortint unsigned val1;
  shortint unsigned val2;
  int result; 
  int txn_id;

  function new(op_type_t _op = ADD, shortint unsigned _v1 = 0, 
              shortint unsigned _v2 = 0);
    mode = _op;
    val1 = _v1;
    val2 = _v2;
  endfunction

  function alu_txn clone();
    alu_txn other = new this;
    return other;
  endfunction

  function void init_txn(op_type_t m = ADD,
                         shortint unsigned v1 = 0,
                         shortint unsigned v2 = 0,
                         int id = 0);
    mode = m;
    val1 = v1;
    val2 = v2;
    txn_id = id;
  endfunction

endclass

