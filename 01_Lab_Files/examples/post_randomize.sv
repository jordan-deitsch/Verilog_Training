
module post_randomize;

class pkt;
bit [7:0] addr,last_addr;

constraint not_equal {
  addr != last_addr;
}

function void post_randomize();
  last_addr = addr;
endfunction

endclass

pkt p;

initial begin
 p = new();
 for (int i = 0; i<20; i++) begin
   p.randomize();
   $display("addr = %0d",addr);
 end
end
endmodule
