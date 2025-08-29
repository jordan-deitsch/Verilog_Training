package my_templates;
  let check_mutex(a, b) = $display( !(a && b) );
  let valid_arb(request, valid, override) = |(request & valid) || override;
endpackage

module my_chip ();
import my_templates::*;

always_comb begin
  check_mutex(read_enable, write_enable);
  if (valid_arb(.request(start), .valid(d_ok), .override(abort))) 
  begin
    $display ("Starting Arb");
  end
end


endmodule
