#Makefile for sva_uart lab

SOURCES = test_u_xmit.sv  u_xmit.sv

normal: sv_cmp
	vsim -c -assertdebug test_u_xmit -do "run -all"

bad: sv_cmp_bad
	vsim -c -assertdebug test_u_xmit -do "run -all"

gui: sv_cmp
	vsim  -assertdebug test_u_xmit

gui_bad: sv_cmp_bad
	vsim  -assertdebug test_u_xmit

sv_cmp:
	test -e work || vlib work
	vlog +acc=a +define+BAD=0 $(SOURCES)

sv_cmp_bad:
	test -e work || vlib work
	vlog +acc=a +define+BAD=1 $(SOURCES)

run:
	vsim -c -assertdebug test_u_xmit -do "run -all"

###################
## VCS
PLATFORM=$(shell arch)
ifeq "$(PLATFORM)" "x86_64"
VCS =    vcs -full64
else
VCS = vcs
endif

VCS_ARGS =     -sverilog -timescale=1ns/1ns -debug_access+all +warn=noTMPO +define+SNPS +define+TRACE_ON=0 +define+BAD=0 +define+VPDDUMP=1
VCS_BAD_ARGS = -sverilog -timescale=1ns/1ns -debug_access+all +warn=noTMPO +define+SNPS +define+TRACE_ON=0 +define+BAD=1 +define+VPDDUMP=1
XVLOG_ARGS = -d BAD=0
XVLOG_BAD_ARGS = -d BAD=1

vcs:
	$(VCS) $(VCS_ARGS) $(SOURCES)
	./simv

vcs_bad:
	$(VCS) $(VCS_BAD_ARGS) $(SOURCES)
	./simv


vcs_gui:
	$(VCS) $(VCS_ARGS) $(SOURCES) -gui
	./simv

vcs_gui_bad:
	$(VCS) $(VCS_BAD_ARGS) $(SOURCES) -gui
	./simv

################
# CDS

irun:
	irun -64bit $(SOURCES) +define+BAD=0

irun_bad:
	irun -64bit $(SOURCES) +define+BAD=1

irun_gui:
	irun -64bit -gui -access r  +define+BAD=0 $(SOURCES)

irun_gui_bad:
	irun -64bit -gui -access r  +define+BAD=1 $(SOURCES)


xrun:
	xrun -64bit $(SOURCES) +define+BAD=0

xrun_bad:
	xrun -64bit $(SOURCES) +define+BAD=1

xrun_gui:
	xrun -64bit -gui -access r  +define+BAD=0 $(SOURCES)

xrun_gui_bad:
	xrun -64bit -gui -access r  +define+BAD=1 $(SOURCES)

################
# Vivado
#

viv: viv_cmp
	xsim -R sim

viv_bad: 
	xvlog -d BAD=1 -sv  $(SOURCES) 
	xelab test_u_xmit -s sim
	xsim -R sim

viv_gui: 
	xvlog -d BAD=0 -sv $(SOURCES) 
	xelab test_u_xmit -s sim -debug all
	xsim sim -gui

viv_gui_bad: 
	xvlog -d BAD=1  -sv $(SOURCES) 
	xelab test_u_xmit -s sim -debug all
	xsim sim -gui

viv_cmp:
	xvlog -d BAD=0 -sv  $(SOURCES) 
	xelab test_u_xmit -s sim


###################
## Common

clean:
	rm -rf  *.tmp  *.log  log transcript work *.wlf vsim.fcdb *.vstf \
	rm -rf *~ core csrc simv* vc_hdrs.h ucli.key urg* *.log core.*
	rm -rf DVEfiles inter.vpd
	rm -rf xcelium.d xrun.* irun.*
	rm -rf webtalk_* xelab.* xsim_* xvlog.*
	rm -rf webtalk.* webtalk_* xelab.* xsim.* xsim_* xvlog.* vivado_* vivado.* sim.wdb .Xil



