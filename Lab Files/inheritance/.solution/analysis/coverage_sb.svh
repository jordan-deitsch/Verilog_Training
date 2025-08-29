
//-------------------------------------------
// coverage scoreboard
// tracks functional coverage

class coverage_sb;

 mailbox #(Packet_base) mon2cov;  // mailbox handle

 router_coverage r_cov;
 int txn_cnt;
 real current_coverage;
 int percentage_100_cnt;
 bit percentage_100_met;
 
 function new();
   r_cov = new();
 endfunction

 task run();
   Packet_base temp;
   Packet txn;
   forever  begin
     mon2cov.get(temp);
     $cast(txn, temp); // cast so can access all the properties
     txn_cnt++;
     r_cov.sample(txn);
     current_coverage = r_cov.get_coverage();
     if(current_coverage == 100 && !percentage_100_met) begin
       percentage_100_cnt = txn_cnt;
       percentage_100_met = 1;
     end
     if(verbosity >= DEBUG)
       $display("%0d Packets sampled,  Coverage = %f%% ",
                txn_cnt,current_coverage);
   end
 endtask 
 
 function void report();
  if(verbosity >= MEDIUM) begin
    $display("\n********************************");
    $display(" Final Coverage = %f%% ",current_coverage);
    if(percentage_100_met)
      $display(" 100%% Coverage met with %0d transactions",
       percentage_100_cnt);
    $display("********************************\n"); 
  end 
 endfunction

endclass
