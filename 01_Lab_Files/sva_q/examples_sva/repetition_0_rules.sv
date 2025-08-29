`define true 1
module repetition_0_rules;
bit a = 0;
bit b = 0;
bit c = 0;
bit clk = 0;


always #20 clk = !clk;


initial begin
//  $vcdpluson;
// rep_0_rule_1
  @ (negedge clk) a = 1;
  @ (negedge clk) a = 0;
// rep_0_rule_2
  @ (negedge clk) c = 1;
  @ (negedge clk) c = 0;
// rep_0_rule_3
  @ (negedge clk) b = 1;
  @ (negedge clk) b = 0;
  
//
  @ (negedge clk) $stop;
end

//************ Rule 1
property p_rep_0_rule_1;
  @(posedge clk) a ##1 ( b[*0] ##0 c );
endproperty

a_rep_0_rule_1:  assert property(p_rep_0_rule_1);
// This assertion generates the following message from VCS:
// "Assertion a_rep_0_rule_1 has no states and hence it will not be simulated"

//************ Rule 2
property p_rep_0_rule_2;
  @(posedge clk) (a ##0 b[*0] ) ##1 c;
endproperty

a_rep_0_rule_2:  assert property(p_rep_0_rule_2);
// This assertion generates the following message from VCS:
// "Assertion a_rep_0_rule_2 has no states and hence it will not be simulated"

//************ Rule 3
property p_rep_0_rule_3;
  @(posedge clk) (a[*0] ##2 b);
endproperty

property p_rep_0_rule_3_equiv;
  @(posedge clk) ##1 b;
endproperty

a_rep_0_rule_3:        assert property(p_rep_0_rule_3);
a_rep_0_rule_3_equiv:  assert property(p_rep_0_rule_3_equiv);

//************ Rule 4
property p_rep_0_rule_4;
  @(posedge clk) a |-> (a ##2 b[*0]);
endproperty

property p_rep_0_rule_4_equiv;
  @(posedge clk) a|-> (a ##1 1);
endproperty

a_rep_0_rule_4:        assert property(p_rep_0_rule_4);
a_rep_0_rule_4_equiv:  assert property(p_rep_0_rule_4_equiv);

//************ [*0:M]

property p_rep_0_rule_range;
  @(posedge clk) (a[*0:1] ##1 b ##1 c);
endproperty

a_rep_0_rule_range:        assert property(p_rep_0_rule_range);


endmodule
