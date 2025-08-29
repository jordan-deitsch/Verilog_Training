module param_class_inherit();

class D_base #( type T = int );
  T payload [512];
endclass

//derived from default specialization of D_base
class D_1 extends D_base ;  // T is int
endclass
D_1 D_1_handle = new();

//derived from specialization of D_base
class D_2 extends D_base #(.T(string) );  // T is string
endclass
D_2 D_2_handle = new();

//generic class derived from default specialization of D_base
class D_3 #( type R = bit ) extends D_base; // T is int
endclass
D_3  D_3_handle = new();

//generic class derived from default specialization of D_base
class D_4 #( type R = bit ) extends D_base #(.T(R));    //T is R
endclass
D_4 #(.R(byte))  D_4_handle = new();  // T is byte


endmodule
