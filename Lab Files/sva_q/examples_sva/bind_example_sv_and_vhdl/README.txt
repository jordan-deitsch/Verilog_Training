The  example here uses the same SVA container file
(my_svas.sv) and same test bench (bind_example.sv) to 
work with either a sv (my_design.sv) or vhdl (my_design.vhd)
design.  The target design is connected via an sv interface

To compile and run sv target:
$ make
    or
$ make gui

To compile and run VHDL target:
$ make vhdl_target
    or 
$ make vhdl_gui
