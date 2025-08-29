module lifetime;

static int svar;
// automatic int avar;    // illegal

initial
  begin
    static int svar2;
    automatic int avar2; 
  end

task automatic autotask;
  automatic int avar3;		// automatic by default
//  static int svar3;

endtask


initial
  $monitor (svar);
//  $monitor  (svar2,,avar2);  // illegal, not visible outside begin-end

endmodule
