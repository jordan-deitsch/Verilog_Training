# Makefile for Tests
# default target (normal) will compile all tests and run test_std_stim_gen
# cmp target will compile only all tests
# other targets will vsim only a specific test


SOURCES =   \
        alu_pkg.sv \
        alu_rtl.sv alu_bfm_if.sv \
        top.sv

################
# Questa
#

default_targ: cmp
	vsim $(VSIM_DPI) -c -voptargs="+acc" top -do "run -all"
gui: cmp
	vsim $(VSIM_DPI) -voptargs="+acc" top

cmp: sv_compile

sv_compile:
	test -e work || vlib work
	vlog +acc -O0 $(SOURCES)


################
# Common

clean:
	rm -rf  *.tmp  *.log  log transcript work *.wlf vsim.fcdb *.vstf \
	rm -rf *~ core csrc simv* vc_hdrs.h ucli.key urg* *.log core.*
	rm -rf DVEfiles inter.vpd

################
# VCS

PLATFORM=$(shell arch)
ifeq "$(PLATFORM)" "x86_64"
VCS = vcs -full64
else
VCS = vcs
endif

SIMV = 	./simv  -l vcs.log

COMMON_VCS = \
	-sverilog -timescale=1ns/1ns \
	+vpi -debug_access+all +define+SNPS \
	+verilog1995ext+.v

vcs:
	$(VCS) $(COMMON_VCS) $(SOURCES)
	$(SIMV)

vcs_gui:
	$(VCS) $(COMMON_VCS) $(SOURCES) -gui
	$(SIMV)
