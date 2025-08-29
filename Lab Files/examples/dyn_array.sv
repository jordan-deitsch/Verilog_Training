module dyn_array();
  
  
bit [3:0] nibble[ ];	// Dynamic array of 4-bit vectors
int data[ ];            // Dynamic array of int

initial begin
  nibble = new[100];    // resize to 100-element array, default values
  data = new [256];	// resize to 256-element array, default values
end

int addr[ ] = new [50];	// Create a 50-element array
int other_addr[];  //declare another array

initial begin
  for (int i=0; i<addr.size(); i++)
    addr[i] = i;  // write to addr;
  $display("addr size = %0d, addr[1] = %0d", addr.size(), addr[1]);
  addr = new [100];	// Create a 100-element array 
  $display("addr size = %0d, addr[1] = %0d", addr.size(), addr[1]);
  for (int i=0; i<addr.size(); i++)
    addr[i] = i+100;  // write to addr;
  $display("addr size = %0d, addr[1] = %0d", addr.size(), addr[1]);
  addr = new [200] (addr);	// Create a 200-element array preserving previous 
	// values in lower 100 addresses
  $display("addr size = %0d, addr[1] = %0d", addr.size(), addr[1]);
  other_addr = addr;
  $display("other_addr size = %0d, other_addr[1] = %0d", other_addr.size(), other_addr[1]);
  other_addr[5] = 55;
  $display("addr size = %0d, addr[5] = %0d", addr.size(), addr[5]);
  addr[6] = 66;
  $display("addr size = %0d, addr[6] = %0d", addr.size(), addr[6]);
  
  addr.delete();
  $display("addr size = %0d, addr[1] = %0d", addr.size(), addr[1]);
  $display("other_addr size after delete on addr = %0d, other_addr[1] = %0d", other_addr.size(), other_addr[1]);
  $display();

end


int fix_sz_array[200];
int dyn_array[] = new[100];
int an_array[];
bit [31:0]  odd_size[] = new[87];

initial begin
  dyn_array[4] = 44;
  an_array = dyn_array; // same as next line
  $display("0: an_array[4] = %0d",an_array[4]);
  an_array = new[dyn_array.size()](dyn_array);  // same as line above
  an_array[2] = 222;  //init a value
  an_array = new[150];  // resize array - lose contents
  $display("1: an_array[2] = %0d",an_array[2]);
  an_array[3] = 333;  // init a value
  an_array = new[200](an_array);  // resize array - save contents
  $display("2: an_array[3] = %0d",an_array[3]);
  dyn_array = fix_sz_array;	// OK  same type and size
  
  odd_size = fix_sz_array;      // type check error - different size
end  



initial begin
end  


int my_addr[ ] = new[256];
initial begin
  $display("Size of my_addr = %0d", my_addr.size() );
  my_addr.delete(); 
  $display("Size of my_addr (after delete) = %0d", my_addr.size() );
end

    
endmodule
