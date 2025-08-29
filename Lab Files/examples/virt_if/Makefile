# Makefile
SOURCES =  ./types.sv ./dut_if.sv ./dut.sv ./top.sv

normal: sv_cmp
	vsim -c  top -do "run -all"

gui: sv_cmp
	vsim  top

sv_cmp:
	test -e work || vlib work
	vlog $(SOURCES)

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
