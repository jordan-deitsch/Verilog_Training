module q_fifo( input  logic [7:0] data_in, output bit empty, full,
               logic [7:0] data_out,  input event write_fifo, read_fifo );

logic [7:0] q [$];	//  Declare the queue q 
always @ (write_fifo)	//  the write_fifo event 
  if(full)
    $display ("tried to write a full fifo");
  else begin
    q.push_front(data_in);	// write to left end of q
    if(q.size > 7)
      full = 1;	// set as full
    empty = 0;  // set as not empty
  end
always @ (read_fifo)	// the read_fifo event
 if(empty)
   $display("tried to read an empty fifo");
 else begin
   data_out <= q.pop_back();	 // remove   
   full = 0;	 // not full after a read     
   if(q.size() == 0)                       
     empty = 1; 	// set as empty                          
 end       
endmodule
