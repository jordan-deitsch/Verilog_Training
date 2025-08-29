
class coverage_sb;

 mailbox #(wb_txn) mon2cov;
 mem_coverage m_cov;
 int txn_cnt;
 real current_coverage;
 int percentage_100_cnt;
 bit percentage_100_met;

 function new();
   m_cov = new();
 endfunction

 task run();
   wb_txn txn;
   forever begin
     mon2cov.get(txn);
     txn_cnt++;
     m_cov.sample(txn);
     current_coverage = m_cov.get_coverage();
     if(current_coverage == 100 && !percentage_100_met) begin
       percentage_100_cnt = txn_cnt;
       percentage_100_met = 1;
     end
     if(verbosity >= MEDIUM)
       $display("Current coverage = %f", current_coverage );
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

