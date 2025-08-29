# Makefile for DPI examples

normal: cmp
	vsim -c export_ex1 -do "run -all"

cmp:
	test -e work || vlib work
	vlog export_ex1.sv my_lib.c

vcs:
	vcs -full64 -sverilog export_ex1.sv my_lib.c
	./simv

xrun:
	xrun -64bit export_ex1.sv my_lib.c

clean:
	rm -rf  *.tmp  *.log  log transcript work *.wlf vsim.fcdb
	rm -rf  simv ucli.key vc_hdrs.h csrc simv.daidir
	rm -rf  xrun.* xcelium.*

