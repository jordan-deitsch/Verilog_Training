// Router BFM
//--------------------

interface router_bfm #(int sz_router = 8)
                     (input bit clk);
  logic  rst ;
  logic [sz_router-1:0] valid ;
  logic [sz_router-1:0] stream_i ;
  logic [sz_router-1:0] stream_o ;
  logic [sz_router-1:0] busy ;
  logic [sz_router-1:0] valid_o ;
  
 task automatic write_router( input bit[7:0] txn_src_id,
                              input bit[7:0] txn_dest_id,
                              input bit[7:0] txn_payload[],
                              input int txn_pkt_id );
   bit[31:0] temp_transaction_id;
   int port_id;
   port_id = txn_src_id;
   @(negedge clk);
   if (busy[port_id]) begin // busy? 
    valid[port_id] = 0; // clear valid bit
    @(negedge busy[port_id]) // Yes - wait until not busy
    @(negedge clk);  //sync up to clk
   end
   // send start bit
   valid[port_id] = 1; // set valid bit
   stream_i[port_id] = 1; //start bit

   // send dest_id (4 bits), msb first
   for(int i=3; i>=0; i--) 
    @(negedge clk)
     stream_i[port_id] = txn_dest_id[i];

   //send dummy bit to allow busy check
   @(negedge clk);
   stream_i[port_id] = 1;

   // check to make sure router not busy
   @(negedge clk);
   if (busy[port_id]) begin // busy? 
     valid[port_id] = 0; // clear valid bit
     @(negedge busy[port_id]) // Yes - wait until not busy
     @(negedge clk);  // wait one clk to sync
     valid[port_id] = 1; // set valid bit
   end
   // send src_id
   for(int i=3; i>=0; i--) begin
     stream_i[port_id] = txn_src_id[i];
     @(negedge clk);
   end

   // send transaction_id
   temp_transaction_id = txn_pkt_id;
   for(int i=31; i>=0; i--) begin
    stream_i[port_id] = temp_transaction_id[i];
    @(negedge clk);
   end

   // send payload
   for(int i=0; i<txn_payload.size(); i++)
    for(int j=7; j>=0; j--) begin
     stream_i[port_id] = txn_payload[i][j];
     @(negedge clk);
    end
   valid[port_id] = 0; // clear valid bit
 endtask
 
 task automatic read_router_port(input int port_id,
                                 output bit[7:0] txn_src_id,
                                 output bit[7:0] txn_dest_id,
                                 output bit[7:0] txn_payload[],
                                 output int txn_pkt_id );
  bit[7:0]  temp_data;
  bit[7:0]  temp_payload[$];
  bit[31:0] temp_transaction_id;
   
   // set dest_id
   txn_dest_id = port_id;

   // wait valid_o bit true
   wait(valid_o[port_id]);

   // start bit (ignore it)
   @(negedge clk); 

   // get src_id 
   @(negedge clk); //wait until the next clk     
   for(int i=3; i>=0; i--) begin 
    txn_src_id[i] = stream_o[port_id];     
    @(negedge clk);
   end
   // get transaction_id 
   for(int i=31; i>=0; i--) begin
    temp_transaction_id[i] = stream_o[port_id];
    @(negedge clk);
   end
   txn_pkt_id = temp_transaction_id;

   // get payload
   temp_payload = '{ }; //reset size of array to 0;
   while(valid_o[port_id]) 
    begin
     for(int i=7; i>=0; i--) 
      begin
       temp_data[i] =  stream_o[port_id];
       @(negedge clk);
      end
      temp_payload.push_back(temp_data);
    end

   // set up payload
   txn_payload = new[temp_payload.size()]; // resize array
   txn_payload = temp_payload; 
   txn_dest_id = port_id; // set dest to transactor id 
 endtask

endinterface
