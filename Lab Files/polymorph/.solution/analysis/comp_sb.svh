
class comp_sb;

  mailbox #(Packet_base) mb_0;   // mailbox handle
  mailbox #(Packet_base) mb_1;   // mailbox handle
  
  Packet_base mem [int];  // assoc array
  int error_cnt;
  int match_cnt;
  int missing_cnt;
  
  task run();
    fork
      proc(mb_0, "0");
      proc(mb_1, "1");
    join
  endtask

  task proc(ref mailbox #(Packet_base) mb, input string id);
    Packet_base txn, temp_txn;
    forever begin
      mb.get(txn);
      if (!mem.exists(txn.pkt_id)) begin
        // no - put in array
        mem[txn.pkt_id] = txn;
        continue;
      end
      else begin // yes compare
        if(!txn.compare(mem[txn.pkt_id])) begin // error
          error_cnt++;
          if(verbosity >= MEDIUM)
            $display("Proc %s, Packet Mismatch:  #1: %s #2: %s", 
                      id,
                      txn.convert2string(),
                      mem[txn.pkt_id].convert2string());      
        end
        else begin
          match_cnt++;
          if(verbosity >= HIGH)
            $display("Packet Match, pkt_id = %0d", txn.pkt_id);
        end
        mem.delete(txn.pkt_id);  //remove entry
      end
    end            
  endtask


 function void report();
  if(verbosity >= MEDIUM) begin
    $display("\n********************************");
    $display("Matches:    %0d", match_cnt);
    $display("Mismatches: %0d", error_cnt);
    $display("Missing:    %0d \n", mem.num());
    $display("********************************\n"); 
  end
 endfunction

 endclass

