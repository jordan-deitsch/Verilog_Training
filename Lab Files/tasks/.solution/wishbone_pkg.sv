package wishbone_pkg;

  typedef enum  {NONE, WRITE, READ, RMW, WAIT_IRQ } wb_txn_t;


  typedef struct {
    wb_txn_t  txn_type;
    bit[31:0] adr;
    logic[31:0] data;
    int unsigned count;
    bit[7:0] byte_sel;
  } wb_txn;


endpackage
