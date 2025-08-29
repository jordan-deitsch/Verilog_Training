module this_ex;

class Packet;
 integer status;

 function void copy(input Packet p);
   this.status  = p.status; // copy properties of object p to this object

 endfunction

 virtual function Packet clone();
   Packet temp = new;	// create new Packet object
   temp.copy(this);	// copy properties of this object to new object
   return(temp);	//return cloned object
 endfunction 

endclass

Packet orig_pkt, cloned_pkt;

initial begin
  Packet orig_pkt = new();
  orig_pkt.status = 55;
  cloned_pkt = orig_pkt.clone();
  $display("cloned_pkt.status = %0d",cloned_pkt.status);
end

endmodule
