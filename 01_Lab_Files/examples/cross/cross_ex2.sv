module cross_ex;
bit clk;

typedef enum {s1,s2,s3} sts;
typedef enum {a,b,c} mds;
sts state;
mds mode;

covergroup cga() @(posedge clk);
  cp_state: coverpoint state;
  cp_mode:  coverpoint mode;
  cs_modstat: cross cp_state, cp_mode;
  
endgroup

covergroup cgb() @(posedge clk);
  cp_state: coverpoint state{
           bins s1_bin = {s1};
           bins s2_bin = {s2};
           bins s3_bin = {s3};
  }
  cp_mode: coverpoint mode{
           bins a_bin = {a};
           bins b_bin = {b};
           bins c_bin = {c};
  }
  cs_modstat: cross cp_state, cp_mode{
    bins band = binsof(cp_state.s3_bin) && binsof(cp_mode.c_bin);
//    bins bor  = binsof(cp_state.s2_bin) || binsof(cp_mode.c_bin);
    bins bint = binsof(cp_state) intersect {[s1:s2]};
    ignore_bins bout = binsof(cp_state.s2_bin) && binsof(cp_mode.b_bin);
  
  }
  
endgroup

cga cg1, cg2;

initial
  repeat (4) begin
    @(posedge clk);
    state = s1;
    @(posedge clk);
    state = s2;
    @(posedge clk);
    state = s3; 
    #200 $stop;  
  end

initial
  begin
    mode = a;
    repeat (2)@(negedge clk);
    mode = b;
    repeat (2)@(negedge clk);
    mode = c;   
  end

always @ (posedge clk)
  $display($stime, "  state = %s, mode = %s", state.name(), mode.name());


initial
  begin
    cg1 = new();
    cg2 = new();
    clk = 0;
    forever #20 clk = !clk;
  end  

endmodule
