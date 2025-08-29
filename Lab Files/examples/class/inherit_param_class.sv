module inherit_param_class;

class AA #( int size = 512 );
  byte payload [size];
endclass

class aa_derived extends AA ;
endclass

aa_derived aa_derived_handle = new();

class aa_derived_2 extends AA #(.size(200) );
endclass

aa_derived_2 aa_derived_handle_2 = new();

endmodule
