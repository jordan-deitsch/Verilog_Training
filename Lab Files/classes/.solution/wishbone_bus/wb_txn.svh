
//----------------------------------------
// Wishbone bus transaction type
// Mike Baird
//-----------------------------------------
  // Wishbone transaction types enumeration
  // typedef enum  {NONE, WRITE, READ, RMW, WAIT_IRQ } wb_txn_t;
  // UVM status enumeration
  // typedef enum {IS_OK, NOT_OK} status_e;

class wb_txn;

  rand wb_txn_t     txn_type;
  status_e          t_status;
  rand bit[31:0]    adr;
  rand logic[31:0]  data[1];
  rand int unsigned count;
  bit[7:0]          byte_sel;
  
  function new(wb_txn_t t_type = NONE, bit[31:0] addr = 0,
              logic[31:0] dat = -1 ); //or  = null
    txn_type = t_type;
    adr = addr;
    data[0] = dat;
    byte_sel = 4'b1111; // only valid value for byte_sel
    count = 1;
  endfunction
  
//  constraint data_sz {data.size() == count; }


  function void init_txn( wb_txn_t op = NONE, bit[31:0] l_adr = 0,
                      logic[31:0] l_data[], cnt = 1);
    txn_type = op;
    adr = l_adr;
    data = l_data;
    count = cnt;
  endfunction
    
  function wb_txn clone();
    wb_txn temp = new();
    temp.copy(this);
    return(temp);
  endfunction
  
  function string convert2string();
    string str1;
    
    str1 = {    "-------------------- Start WISHBONE txn --------------------\n",
                "WISHBONE txn \n",
      $sformatf("  txn_type : %s\n", txn_type.name()),
      $sformatf("  t_status : %s\n", t_status.name()),
      $sformatf("  adr      : 'h%h\n", adr),
      $sformatf("  count    : 'h%h\n", count),
      $sformatf("  byte_sel : 'h%h\n", byte_sel)};
      foreach(data[i])
         str1 = {str1, $sformatf("  data[%0d]  : 'h%h\n", i, data[i])};
      str1 = {str1, "--------------------- End WISHBONE txn ---------------------\n"};
    return(str1);
  endfunction


  function bit compare(wb_txn rhs);
    wb_txn rhs_;
    compare = (
      adr      == rhs.adr    &&
      data     == rhs.data   &&
      count    == rhs.count  
    );
   endfunction

  function void copy(wb_txn rhs);
    adr      = rhs.adr     ;
    data     = rhs.data    ;
    count    = rhs.count   ;
    txn_type = rhs.txn_type; 
    t_status = rhs.t_status; 
    byte_sel = rhs.byte_sel;
  endfunction

 function void print();
  $display(convert2string()); // print out string
 endfunction


endclass

