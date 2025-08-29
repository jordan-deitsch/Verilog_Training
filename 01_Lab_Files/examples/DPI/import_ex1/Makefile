# Makefile for DPI examples
# NOTE - set QUESTA_HOME to point to the questasim install dir
# QUESTA_HOME /home/tools/questasim

AFILES =  ./array_handles.sv

ifndef QUESTA_HOME
  $(error The QUESTA_HOME environment variable is not set)
endif

normal: clean cmp
	vsim -c import_ex1 -do "run -all"

cmp:
	test -e work || vlib work
	vlog import_ex1.sv  my_lib.c

vcs:
	vcs -full64 -sverilog import_ex1.sv my_lib.c
	./simv

xrun:
	xrun -64bit import_ex1.sv my_lib.c

clean:
	rm -rf  *.tmp  *.log  log transcript work *.wlf vsim.fcdb
	rm -rf  simv ucli.key vc_hdrs.h csrc simv.daidir
	rm -rf  xrun.* xcelium.*
