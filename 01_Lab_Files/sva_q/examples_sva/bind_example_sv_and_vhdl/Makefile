#Makefile for sva_pipe lab

TB = my_if.sv bind_ex.sv my_svas.sv
SV_TARGET = my_design.sv
V_TARGET = my_design.vhd

sv_target: clean sv_cmp
	vsim -c -assertdebug bind_ex

vhdl_target: clean vhdl_cmp
	vsim -c -assertdebug bind_ex

vhdl_gui: clean sv_cmp
	vsim  -assertdebug bind_ex 

gui: clean sv_cmp
	vsim  -assertdebug bind_ex 

sv_cmp:
	test -e work || vlib work
	vlog +acc=a $(TB)
	vlog +acc=a $(SV_TARGET) 

vhdl_cmp:
	test -e work || vlib work
	vlog +acc=a $(TB)
	vcom +acc=a $(V_TARGET) 

run:
	vsim -c -assertdebug bind_ex

	
clean:
	rm -rf  *.tmp  *.log  log transcript work *.wlf vsim.fcdb

nuke: clean
	rm -rf *.v* transcript *.wlf vsim.fcdb


