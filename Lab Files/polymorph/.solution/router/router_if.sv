interface router_if #(int sz_router = 8)
                     (input bit clk);
  logic  rst ;
  logic [sz_router-1:0] valid ;
  logic [sz_router-1:0] stream_i ;
  logic [sz_router-1:0] stream_o ;
  logic [sz_router-1:0] busy ;
  logic [sz_router-1:0] valid_o ;

endinterface: router_if
