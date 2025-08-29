interface class B_Put#(type PUT_T = logic); 
  pure virtual task bput(ref PUT_T arg);
endclass
interface class NB_Put#(type PUT_T = logic); 
  pure virtual function void nbput(PUT_T arg);
endclass

interface class B_Get#(type GET_T = logic); 
  pure virtual task bget(ref GET_T arg);
endclass
interface class NB_Get#(type GET_T = logic); 
  pure virtual function GET_T nbget();
endclass

interface class Get#(type GET_T = logic) extends B_Get#(GET_T), NB_Get#(GET_T) ; 
endclass

interface class Put#(type PUT_T = logic) extends B_Put#(PUT_T), NB_Put#(PUT_T) ; 
endclass


class fifo #(type T = logic, int DEPTH = 1) implements Put#(T), Get#(T);
  T FifoQ[$:DEPTH-1];
				
  virtual task bput(ref T arg);
    wait(FifoQ.size() < DEPTH); 
    FifoQ.push_back(arg);
  endtask
  virtual function void nbput(T arg); 
    FifoQ.push_back(arg);
  endfunction

  virtual task bget(ref T arg);
    wait(FifoQ.size() > 0); 
    arg = FifoQ.pop_front();
  endtask
  virtual function T nbget();
    return(FifoQ.pop_front());
  endfunction
  
endclass

module env;

 fifo #(string,4) my_fifo = new();
 string ins = "Hi There", outs;
 initial
   begin
     my_fifo.nbput(ins);
     outs = my_fifo.nbget();
     $display("\nSimple Test: %s\n",outs);   // single non-blocking put/get

     ins = "Hello"; 
     $display("Interleaved (blocking) burst test (Burst:5 Fifo Depth:4):\n");
     fork  
       repeat(5) begin
     	 my_fifo.bput(ins);
         $display("\tPut: %s:",ins);	// 5 puts
       end
       repeat(6) begin
     	 my_fifo.bget(outs);
         $display("\tGet: %s:",outs);	// 6 gets (in parallel)
       end
     join_none
     #0;
     $display("\nOne more put \"Goodbye\"");
     ins = "Goodbye";
     my_fifo.bput(ins);
   end

endmodule
