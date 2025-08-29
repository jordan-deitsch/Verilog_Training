
module enum_types;
typedef enum {red, green, blue, yellow, white, black} colors ;
colors my_colors;
initial begin
  my_colors = green;
//  my_colors = 1;  // invalid  need to typecast
//  my_colors = colors'(2);  // cast as blue
  case (my_colors) 
    red:  $display ("my_color is red");
    blue:  $display ("my_color is blue");
    default:  $display ("my_color is not blue or red");
  endcase	
end
endmodule
