
program test;

typedef enum bit[3:0] {IDLE, WRITE, READ} cmd_type ;
typedef enum bit {OK, ERROR} status_type;

class Packet ;
  //properties
  cmd_type command;
  int unsigned address;
  status_type status;

  // initialization
  function new(int addr);
    command = READ;
    address = addr;
    status = OK;
  endfunction

  // methods
  // public access entry points
  task clean();
    command = IDLE; address = 0; 
  endtask
endclass


Packet pkt;    // declare object handle

initial
  pkt = new(0); // create object at handle
  
initial begin  
  pkt = new(2); 
  pkt = new(4);
  pkt = null;
end
endprogram
