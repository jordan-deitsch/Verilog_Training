#Makefile for sva_pipe lab

SOURCES = types_pkg.sv test_sm.sv beh_sram.v sm_seq.v      sm.sv sva_container.sv
BAD =     types_pkg.sv test_sm.sv beh_sram.v sm_seq.v  bad_sm.sv sva_container.sv

###################
## Questasim

normal:  sv_cmp
	vsim -c -assertdebug test_sm -do "run -all"

gui:  sv_cmp
	vsim  -assertdebug test_sm

sv_cmp:
	test -e work || vlib work
	vlog -incr +acc=a $(SOURCES)

bad:
	test -e work || vlib work
	vlog -incr +acc=a $(BAD)
	vsim  -c -assertdebug test_sm -do "run -all"

gui_bad:
	test -e work || vlib work
	vlog -incr +acc=a $(BAD)
	vsim  -assertdebug test_sm

run:
	vsim -c -assertdebug test_sm



###################
## VCS
PLATFORM=$(shell arch)
ifeq "$(PLATFORM)" "x86_64"
VCS =    vcs -full64
else
VCS = vcs
endif

VCS_ARGS = -sverilog -timescale=1ns/1ns +warn=noTMPO +define+SNPS +define+TRACE_ON=0 +acc


vcs:
	$(VCS) $(VCS_ARGS) $(SOURCES)
	./simv

vcs_gui:
	$(VCS) $(VCS_ARGS) $(SOURCES) -gui
	./simv

vcs_bad:
	$(VCS) $(VCS_ARGS) $(BAD)
	./simv

vcs_gui_bad:
	$(VCS) $(VCS_ARGS) $(BAD) -gui
	./simv

################
# CDS

irun:
	irun -64bit $(SOURCES)

irun_bad:
	irun -64bit $(BAD)

irun_gui:
	irun -64bit -gui -access r  $(SOURCES)

irun_gui_bad:
	irun -64bit -gui -access r  $(BAD)

xrun:
	xrun -64bit $(SOURCES)

xrun_bad:
	xrun -64bit $(BAD)

xrun_gui:
	xrun -64bit -gui -access r  $(SOURCES)

xrun_gui_bad:
	xrun -64bit -gui -access r  $(BAD)

################
# Vivado
#

viv: viv_cmp
	xsim -R sim

viv_bad: viv_cmp_bad
	xsim -R sim

viv_gui: 
	xvlog -d BAD=0 -sv $(SOURCES) 
	xelab test_sm -s sim -debug all
	xsim sim -gui

viv_gui_bad: 
	xvlog -d BAD=1  -sv $(SOURCES) 
	xelab test_sm -s sim -debug all
	xsim sim -gui

viv_cmp:
	xvlog -d BAD=0 -sv  $(SOURCES) 
	xelab test_sm -s sim

viv_cmp_bad:
	xvlog -d BAD=0 -sv  $(BAD) 
	xelab test_sm -s sim

###################
## Common

clean:
	@echo "Cleaning up files..."
	rm -rf DVEfiles *.tmp  *.log  log transcript work *.wlf vsim.fcdb *.vpd
	rm -rf *~ core csrc simv* vc_hdrs.h ucli.key urg* *.log core.*
	rm -rf xcelium.d xrun.* irun.*
	rm -rf web* xelab* xsim* xvlog*
