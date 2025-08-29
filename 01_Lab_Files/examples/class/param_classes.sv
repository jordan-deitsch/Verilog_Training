
module param_classes;

class AA #( int size = 512 );
  byte payload [size];
endclass


AA aa_512 = new();  //Creates a default specialization of generic class AA
AA #(.size(256)) my_aa = new(); //Creates a specialized (new or different) type

initial begin
  my_aa = aa_512;   //Illegal assignment (run time error) from one object type
end                   // to another

//Parameterization of a type:
class BB #( type T = int );
  T payload [512];
endclass
BB bb_int = new();		// default specialization
BB #(string) bb_string = new();	// specialized type 

//Multiple parameters:
class CC #( type T = int, int size = 512 );
  T payload [size];
endclass

CC #(.T(integer), .size(1024)) cc_handle = new();  // type integer and size 1024


initial begin
//  bb_int = bb_string;  //Illegal assignment (run time erro) from one object type
end                      // to another


endmodule
