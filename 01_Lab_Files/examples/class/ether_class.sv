class ether_packet;

// Ethernet Packet Fields
  bit[55:0] preamble = 'h55555555555555;
  bit [7:0] sfd = 'hab;
  bit[47:0] dest;
  bit[47:0] src;
  bit[15:0] len;
  bit [7:0] payld [ ];

function new(int i);
    payld = new[i];
    len = i;
endfunction : new

  task load_frame( input [47:0] lsrc, ldest,
  	           input  [7:0] start_dat);
       src = lsrc;
       dest = ldest;
       len = payld.size;
       if(start_dat > 0)
         for(int i = 0; i < len; i++) 
	    payld[i] = start_dat +i;
  endtask : load_frame

  //////////////////////////
  // Pretty-print a Frame 
  //////////////////////////
  function void print;
//      $displayh("\n\t preamble: ", preamble);
//      $displayh("\t      sfd: ", sfd);
      $displayh("\t      src: ", src);
      $displayh("\t     dest: ", dest);
      $displayh("\t      len: ", payld.size);
         for(int i = 0; i < len; i++) 
            $displayh("\t payld[%0h]: %0h",i,payld[i]); 
      $displayh("");
  endfunction : print

endclass : ether_packet

program test_ether();

ether_packet ep ;

initial
  begin
    ep = new (4);
    ep.load_frame('h55,'h66,'h77);
    ep.print();
    ep = new(1);
    ep.load_frame('h22,'h33,'h44);
    ep.print();
  end



endprogram
