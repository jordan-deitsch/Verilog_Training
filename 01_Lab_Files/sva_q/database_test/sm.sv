/*******************************
*  RTL sm
*/

module sm
    import types_pkg::*;
    ( input  logic clk, rst,
      input  logic [3:0] opcode,
      output logic a_wen_n, wd_wen_n, rd_wen_n, inca);

state_values  state, n_state;

// sequential logic
always @ (posedge clk or posedge rst)
  if (rst)
    state <= IDLE;
  else
    state <= n_state;

// next state logic
always @ (state or opcode)
  case (state)
     IDLE:           // IDLE
           case (opcode)
             NOP: // nop
                     n_state = IDLE;
             WT_WD: // wt_wd
                     n_state = WT_WD_1;
             WT_BLK: // wt_blk
                     n_state = WT_BLK_1;
             RD_WD: // rd_wd
                     n_state = RD_WD_1;
             default: begin
                     n_state = IDLE;
                     $display ("%0d state machine:  illegal op received", $stime());
                     end
           endcase
     WT_WD_1:
         n_state = WT_WD_2;
     WT_WD_2:
         n_state = IDLE;
     WT_BLK_1:
         n_state = WT_BLK_2;
     WT_BLK_2:
         n_state = WT_BLK_3;
     WT_BLK_3:
         n_state = WT_BLK_4;
     WT_BLK_4:
         n_state = WT_BLK_5;
     WT_BLK_5:
         n_state = IDLE;
     RD_WD_1:
         n_state = RD_WD_2;
     RD_WD_2:
         n_state = IDLE;
     default:
         n_state = IDLE;
  endcase

// state machine output logic
function logic calc_a_wen();
  return(!( state == WT_WD_1  ||
            state == WT_BLK_1 ||
            state == RD_WD_1 )
        );
endfunction

always_comb
  a_wen_n = calc_a_wen();
/*
assign a_wen_n = !( state == WT_WD_1  ||
                   state == WT_BLK_1 ||
                   state == RD_WD_1 );
                   */
assign wd_wen_n = !( state == WT_WD_2  ||
                    state == WT_BLK_2 ||
                    state == WT_BLK_3 ||
                    state == WT_BLK_4 ||
                    state == WT_BLK_5 );
assign rd_wen_n = !( state == RD_WD_2);
assign inca = ( state == WT_BLK_3 ||
                state == WT_BLK_4 ||
                state == WT_BLK_5 );

endmodule

