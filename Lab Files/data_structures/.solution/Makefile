#Makefile for simple mem
# Kurt Schwartz

QUESTA_HOME ?= $(dir $(shell which vsim))/..

WB_BUS_SOURCES =  \
        wishbone_pkg.sv wb_slave_mem.sv wishbone_bus_syscon_if.sv  \
        top.sv test.sv

################
# Questa
#

normal: sv_bus_cmp
	vsim  -voptargs="+acc" -t ns -c top test -do "run -all"

gui: sv_bus_cmp
	vsim -t ns -voptargs="+acc" top test

sv_bus_cmp:
	test -e work || vlib work
	vlog +acc -O0 -incr $(WB_BUS_SOURCES)

################
# VCS

PLATFORM=$(shell arch)
ifeq "$(PLATFORM)" "x86_64"
VCS =    vcs -full64
else
VCS = vcs
endif

SIMV = 	./simv -l vcs.log

COMMON_VCS = \
	-sverilog -timescale=1ns/1ns \
	+vpi -debug_access+all +define+SNPS \
	+verilog1995ext+.v

vcs:
	$(VCS)  $(COMMON_VCS) $(WB_BUS_SOURCES)
	$(SIMV)

vcs_gui:
	$(VCS)  $(COMMON_VCS) $(WB_BUS_SOURCES) -gui
	$(SIMV)

################
# CDS

irun:
	irun -64bit $(WB_BUS_SOURCES)

irun_gui:
	irun -64bit -gui -access r +define+SNPS $(WB_BUS_SOURCES)

xrun:
	xrun -64bit -xceligen on $(WB_BUS_SOURCES)

xrun_gui:
	xrun -64bit -gui -access r  -xceligen on $(WB_BUS_SOURCES)


################
# Common

clean:
	rm -rf  *.tmp  *.log  log transcript work *.wlf vsim.fcdb *.vstf \
	rm -rf *~ core csrc simv* vc_hdrs.h ucli.key urg* *.log core.*
	rm -rf DVEfiles inter.vpd
	rm -rf xcelium.d xrun.* irun.*
