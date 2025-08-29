module func_with_return;

initial
  begin
    #10 $display("a: %h b: %h  uniq_vals: %h", 5,4,uniq_vals(5,4));
    #10 $display("a: %h b: %h  uniq_vals: %h", 4,4,uniq_vals(4,4));
    #10 $display("a: %h b: %h  uniq_vals: %h", 4,5,uniq_vals(4,5));
    #10 $display("a: %h b: %h  uniq_vals: %h", 5,5,uniq_vals(5,5));
  end

function uniq_vals (input [7:0] a,b);
uniq_vals = 0;
if (a!= b) 
  return 1;
//else
//  return 0;
endfunction    






endmodule
