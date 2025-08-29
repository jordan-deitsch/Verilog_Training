program assoc_array;



bit i_array[*]; 	        // associative array of bits (unspecified index)
			        // unspecified index (*) implies any integral value
bit [7:0] age [string];      // associative array of 8-bit vectors, indexed by string
	
string tom = "tom";

initial
  begin
    age [tom] =  21;
    age ["joe"] =  32;
    $display("Tom is %d years of age ", age[tom], "[%0d ages available]",age.num());
  end	
	
endprogram
