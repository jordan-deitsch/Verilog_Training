module router_rtl #(sz_router = 8)
                   (input bit[sz_router-1:0]  valid, stream_i,
                    input bit clk, rst,
	            output bit[sz_router-1:0]  busy, valid_o, stream_o);

bit[7:0] out_chan_busy;
semaphore out_busy_s[sz_router];

initial  //create semaphores
  for(int i=0; i<sz_router; i++)
    out_busy_s[i] = new(1);

//router slices
genvar k;
for (k=0; k<sz_router; k++) begin :slices
  slice #(.slice_num(k) ) slice_inst( .*);
end

endmodule

module slice #(parameter slice_num = 0)
              (input logic clk, rst);

bit [3:0] dest;
enum {IDLE, GET_DEST, CHK_DEST, SND_PYLD, CLEANUP } state, next_state;	       
bit[2:0] dest_addr_cnt;
semaphore out_busy_s =new(1);

int bd_cnt;  // for error insertion


// next state logic & output logic
always @(posedge clk)
begin  #1;  //sigh... temp fix for race condition.
  case (state)
   IDLE:     begin                                                       
              dest_addr_cnt = 0;                                           
              dest = '1;  // set to address 15                           
              if (router_rtl.valid[slice_num]) // data coming in?                   
                next_state = GET_DEST;                                   
              else                                                       
                next_state = IDLE; // stay here                          
             end                                                         
   GET_DEST: begin
               if (dest_addr_cnt == 3)
                 next_state = CHK_DEST;
               else
                 next_state = GET_DEST; // stay here
               if (dest_addr_cnt++ < 4 )                              
                 dest = {dest, router_rtl.stream_i[slice_num]}; // get bit       
             end
   CHK_DEST: begin                                                       
              if(router_rtl.out_chan_busy[dest]) begin                 
                router_rtl.busy[slice_num] = 1; // set as busy               
                next_state = CHK_DEST; // stay here                      
              end                                                        
              else                                                       
              if (router_rtl.out_busy_s[dest].try_get()) begin //get key                  
                router_rtl.out_chan_busy[dest] = 1; //set out as busy 
                router_rtl.busy[slice_num] = 0; // set as ! busy               
                router_rtl.valid_o[dest] = 1; //set as valid output
                router_rtl.stream_o[dest] = 1; // set start bit     
                next_state = SND_PYLD; // go to next state              
               end                                                       
              else begin                                                 
                router_rtl.busy[slice_num] = 1; // set as busy                  
                next_state = CHK_DEST; // stay here;                     
              end                                                        
             end                                                         
   SND_PYLD: begin
              if(router_rtl.valid[slice_num]) begin
               router_rtl.busy[slice_num] = 1; // set as busy
               router_rtl.stream_o[dest] = router_rtl.stream_i[slice_num]; // send data
//###########
// Error insertion
   bd_cnt++;
   if(dest == 2 && bd_cnt >40)
     router_rtl.stream_o[dest] = ~router_rtl.stream_i[slice_num]; // send bad data                            
//##########
              end
              else begin
               router_rtl.valid_o[dest] = 0; //clear valid output
               next_state = CLEANUP; // go to cleanup state
              end
             end
   CLEANUP:  begin  // need this state for simultaneous packets
                    // to the same dest port so valid_o can go low one cycle
               router_rtl.out_chan_busy[dest] = 0; //clear out busy 
               router_rtl.busy[slice_num] = 0; // clear input busy               
               router_rtl.out_busy_s[dest].put(); //put the key back
               bd_cnt = 0; // clear bad count
               next_state = IDLE;
             end
  endcase       
end

// seq state logic
always @(posedge clk or posedge rst) begin
  if (rst)
    state <= IDLE;
  else
    state <= next_state;
end

endmodule
