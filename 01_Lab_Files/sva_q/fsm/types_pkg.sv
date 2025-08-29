package types_pkg;
typedef enum logic[3:0] {
  IDLE, WT_WD_1, WT_WD_2, WT_BLK_1, WT_BLK_2,
  WT_BLK_3, WT_BLK_4, WT_BLK_5, RD_WD_1, RD_WD_2
  } state_values;


typedef enum logic[3:0] {NOP, WT_WD, WT_BLK, RD_WD} opcodes;

endpackage
