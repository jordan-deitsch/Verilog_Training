module system_data;

//$num: 	Number of elements in an array
	int q [0:3] = {6,7,8,9};
	initial $display( $length(q,1) );		// prints 4

//$bits: 	Number of bits in a packed array or struct
	bit [3:0] [7:0] aa;
	initial $display( $bits(aa) );		// prints 32

//${left|right}: 	Bounds of a variable
	bit [3:1] [7:4] bb;
	bit [3:1] [7:4] cc [2:0];
	initial begin
	   $display( $left(bb,1), $right(bb,1) );	// prints 3    1
	   $display( $left(cc,1), $right(cc,1) );	// prints 2    0
	end	


endmodule







