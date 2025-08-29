

// LAB:  Declare Packet class



 //LAB:  Declare properties

 
 
 // LAB:  Declare compare function
  

 // LAB:  Declare copy function





 constraint srce {src_id  < ROUTER_SIZE ;}
 constraint dest {dest_id < ROUTER_SIZE ;}
 
 constraint pyld {
   payload.size() inside {[1:5]};
 }
 
 
 
 
 
  // function to init Packet properties
 function void init_txn(
                bit[7:0] s_id,
                bit[7:0] d_id,
                bit[7:0] p_load[],
                int p_id );
   src_id = s_id;
   dest_id = d_id;
   payload = p_load;
   pkt_id = p_id;
 endfunction

function string convert2string();
  string str1;
  str1 = {    "\n-------------------- Start Packet txn --------------------\n",
              "Packet txn:\n",  
    $sformatf("  src_id         : 'h%h\n", src_id),
    $sformatf("  dest_id        : 'h%h\n", dest_id),
    $sformatf("  pkt_id         :  %0d\n", pkt_id),
              "  payload:\n"};
    if(payload.size() < 11 )
      for(int i=0; i<payload.size(); i++)
        str1 = {str1,$sformatf("    payload[%0d] = 'h%h\n", i, payload[i])};
    else  begin
      for(int i=0; i<6; i++) 
        str1 = {str1,$sformatf("    payload[%0d] = 'h%h\n", i, payload[i])};
      str1 = {str1, ". . .\n"};
      for(int i=payload.size()-5; i<= payload.size(); i++)
        str1 = {str1,$sformatf("    payload[%0d] = 'h%h\n", i, payload[i])};
    end 
    
    str1 = {str1,"-------------------- End Packet txn ----------------------\n"};
  return (str1);
 endfunction

 function void print();
  $display(convert2string());
 endfunction
 

endclass
