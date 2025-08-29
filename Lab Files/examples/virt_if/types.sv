package types;

class Packet;
 int field1; 
 function new(int i);
   field1 = i;
 endfunction   
endclass : Packet


class source;
  mailbox #(Packet) out_chan; // null handle
  Packet pkt_to_send;
  int id;
  
  function new(int i);
    id = i;
  endfunction 
   
 task run();
    for(int i = 0; i <= id; i++) begin
      pkt_to_send = new(i);  
      out_chan.put(pkt_to_send);
      $display("source[%0d]: Sent packet with field1 = (%0d)", id, pkt_to_send.field1);  
    end  
  endtask  
endclass : source

class sink;
  mailbox #(Packet) in_chan; // null handle
  virtual dut_if v_dut_if;
  int id = 1;

  function new(virtual dut_if real_dut_if);
     // map virtual interface to real interface
    v_dut_if = real_dut_if;  
  endfunction 
   
  task run();
  Packet stim_pkt;
    while(1) begin
      in_chan.get(stim_pkt);
      // access real interface via virtual IF
      @(negedge v_dut_if.clk)
        v_dut_if.data_rcvd = stim_pkt.field1;
      $display("sink[%0d]:   Received packet with field1 = %0d", id, stim_pkt.field1);  
    end  
  endtask
  
endclass : sink

endpackage
