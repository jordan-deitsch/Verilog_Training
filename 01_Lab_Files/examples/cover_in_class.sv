class packet;

// Ethernet Packet Fields
  bit[7:0] dest, src;
  bit[15:0] len;
  bit [47:0] payld [ ];
  bit valid;

  covergroup cov1 @(valid);    // embedded covergroup
     cp_dest : coverpoint dest;
     cp_src  : coverpoint src;
  endgroup

  function new(int i);
    payld = new[i];  len = i;
    cov1 = new();
  endfunction : new
  
endclass : packet
