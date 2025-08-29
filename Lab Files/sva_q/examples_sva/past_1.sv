
module test_mem;

logic [7:0] in_busData, busAddr;
logic [7:0] out_busData;
bit read,write,clk;

initial begin
  clk = 0;
  read = 0;
  write = 0;
  forever #25 clk = !clk;
end

task read_mem (input int addr, input int num);
  for (int i = 0; i< num; i++) begin
  @ (negedge clk)
    read <= 1;
    busAddr <= addr + i;
  end
  @ (negedge clk) read = 0;
endtask

initial begin
  read_mem(20,5);
  #200 $finish;
end

initial begin
  $vcdpluson;
  $monitor ("%0d out_busData = %d",$time, out_busData);
end

mem mem_inst(.*);
endmodule


module mem ( input logic [7:0] in_busData, 
             input logic [7:0] busAddr,
             output logic [7:0] out_busData, 
             input bit read,write,clk);
             
logic [7:0] pipeData1, pipeData2, mem[0:63];

initial
  for (int i = 0; i<64; i++) mem[i] = i;


always @ (posedge clk) begin
  if (read)
    pipeData1 <= mem[busAddr];
  pipeData2  <= pipeData1;
  out_busData <= pipeData2;
end
    
always @ (posedge clk)
  if(write)
    mem[busAddr] <= in_busData;

sequence s_rd_3;
   ##3 (out_busData == mem[$past( busAddr,3 )]);
endsequence

property p_rd_3;
  @(posedge clk) read |-> s_rd_3;
endproperty

property pd_rd_3;
  logic [7:0] temp;
  @(posedge clk) (read, temp = mem[busAddr]) |->
    ##3 temp == out_busData;
endproperty

a_rd_3:  assert property(p_rd_3);
ad_rd_3: assert property(pd_rd_3);

endmodule
