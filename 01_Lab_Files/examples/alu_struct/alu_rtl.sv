import alu_pkg::*;

module alu_rtl(
  input  shortint unsigned val1, val2,
  input  bit clk,
  input  bit valid_i,
  input  op_type_t mode,
  output bit valid_o,
  output shortint unsigned result
  );
                  
 always @ (posedge clk)
  if(valid_i) begin
   case(mode)
    ADD: result <= #5 val1 + val2;
    SUB: result <= #5 val1 - val2;
    MUL: result <= #5 val1 * val2;
    DIV: result <= #5 val1 / val2;
   endcase
   valid_o <= #5 1; // valid output
  end
  else 
    valid_o <= #5 0; //not valid output
endmodule

