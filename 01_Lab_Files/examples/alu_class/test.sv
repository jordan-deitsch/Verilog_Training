// module test
//-----------------


module test();
import alu_pkg::*;


  test_env t_env;

  initial begin
    t_env = new();
    t_env.build();
    t_env.connect();
    t_env.run();
  end

endmodule
