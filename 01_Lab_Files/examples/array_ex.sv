module array_ex;

bit     [1:0][7:0] PA;
bit     [1:0][7:0] PB;

bit     [7:0] UA  [9:0];
bit     [7:0] UB  [9];

initial
  begin
    $monitor($stime,,"UA[0]: %h, UB[0]: %h",UA[0],UB[0]);
    #10 UA = {default: 'ha};  UB = {default: 'hb};
    #10;
  end

endmodule
