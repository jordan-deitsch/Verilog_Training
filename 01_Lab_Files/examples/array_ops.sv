module array_ops;

bit     [1:0][7:0] PA;
bit     [1:0][7:0] PB;

bit     [7:0] UA  [9:0];
bit     [7:0] UB  [9:0];

bit[1:0][7:0] AA [7:0][7:0];
bit[1:0][7:0] AA [7:0][7:0];

initial
  begin
    PA = 16'haaaa;      PB = 16'hbbbb;
    UA = {default: 'ha};  UB = {default: 'hb};
    $monitor($stime,,"PA: %h, PB: %h, UA[0]: %h, UB[0]: %h",PA,PB,UA[0],UB[0]);
    #10 PA = PB;
    #10 UA = UB;
    #10 PA
  end

endmodule
