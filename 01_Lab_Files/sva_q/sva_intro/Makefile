#Makefile for sva_intro lab

SOURCES = sva_ex.sv

normal: clean compile
	vsim -assertdebug sva_ex

compile:
	test -e work || vlib work
	vlog -incr +acc=a $(SOURCES)

test:   clean compile
	vsim -c -assertdebug sva_ex  -do "run -all; quit"


###################
## VCS

PLATFORM=$(shell arch)
ifeq "$(PLATFORM)" "x86_64"
VCS =    vcs -full64
else
VCS = vcs
endif


VCS_ARGS = -sverilog -timescale=1ns/1ns -debug_access+all +warn=noTMPO +define+SNPS +define+TRACE_ON=0 +define+VPDDUMP=1

vcs:
	$(VCS)  $(VCS_ARGS) $(SOURCES)
	./simv

vcs_gui:
	$(VCS)  $(VCS_ARGS) $(SOURCES) -gui
	./simv

################
# CDS

irun:
	irun -64bit $(SOURCES)

irun_gui:
	irun -64bit -gui -access r +define+SNPS $(SOURCES)

xrun:
	xrun -64bit $(SOURCES)

xrun_gui:
	xrun -64bit -gui -access r +define+SNPS $(SOURCES)

################
# Vivado
#

viv: viv_cmp
	xsim -R sim

viv_gui: 
	xvlog -d BAD=0 -sv $(SOURCES) 
	xelab sva_ex -s sim -debug all
	xsim sim -gui

viv_cmp:
	xvlog -d BAD=0 -sv  $(SOURCES) 
	xelab sva_ex -s sim


###################
## Common

clean:
	rm -rf  *.tmp  *.log  log transcript work *.wlf vsim.fcdb *.vstf \
	rm -rf *~ core csrc simv* vc_hdrs.h ucli.key urg* *.log core.*
	rm -rf DVEfiles inter.vpd
	rm -rf xcelium.d xrun.* irun.*
	rm -rf webtalk_* xelab.* xsim_* xvlog.*
	rm -rf webtalk.* webtalk_* xelab.* xsim.* xsim_* xvlog.* vivado_* vivado.* sim.wdb .Xil



