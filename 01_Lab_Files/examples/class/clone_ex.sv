module clone_ex;

class Packet;
 integer a = 11;

 virtual function Packet clone();
   Packet temp = new this;	// create new Packet object
   return(temp);	//return cloned object
 endfunction 

endclass

class C1;
 integer b = 22;
 Packet pp = new();
 
 virtual function C1 clone();
   C1 temp = new this;	// create new Packet object from current one (shallow copy)
   temp.pp = pp.clone();	// ask pp to clone itself
   return(temp);	//return cloned object
 endfunction 

endclass



C1 orig_c1, shallow_c1, deep_c1;

initial begin
  C1 orig_c1 = new();
  shallow_c1 = new orig_c1;
  
  deep_c1 = orig_c1.clone();
  
  shallow_c1.b = 33;
  shallow_c1.pp.a = 44;
  
  $display("orig_c1.b = %0d",orig_c1.b);
  $display("orig_c1.pp.a = %0d",orig_c1.pp.a);
  $display("deep_c1.b = %0d",deep_c1.b);
  $display("deep_c1.pp.a = %0d",deep_c1.pp.a);
  $stop;
end

endmodule
