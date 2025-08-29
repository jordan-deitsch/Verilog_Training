
virtual class Packet_base;

  // base properties
  int pkt_id;
  
  // API methods for Packets
  pure virtual function string convert2string();
  
  pure virtual function void copy(Packet_base rhs);

  pure virtual  function bit compare(Packet_base rhs);

  pure virtual function void print();


endclass
