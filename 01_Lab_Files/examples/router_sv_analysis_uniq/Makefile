# Makefile for Router DUT


################
# Sub directories

ROUTER_SRCS = ./router
XACTOR_SRCS = ./xactors
TXN_SRCS = ./txn
ANALYSIS_SRCS = ./analysis
STIM_SRCS = ./stim
TOP_SRCS = ./top_modules
ENV_SRCS = ./env

################
# Sources to compile

OTHER_SOURCES = \
              $(TOP_SRCS)/test_params_pkg.sv \
              $(TXN_SRCS)/txn_pkg.sv\
              $(ANALYSIS_SRCS)/analysis_pkg.sv \
              $(XACTOR_SRCS)/xactors_pkg.sv \
              $(STIM_SRCS)/stim_pkg.sv \
              $(ENV_SRCS)/router_env_pkg.sv \
              $(TOP_SRCS)/test.sv \
              $(TOP_SRCS)/top.sv

SOURCES = $(ROUTER_SRCS)/router_bfm.sv \
              $(ROUTER_SRCS)/router_rtl.sv \
              $(OTHER_SOURCES)

BAD_SOURCES = $(ROUTER_SRCS)/router_bfm.sv \
              $(ROUTER_SRCS)/router_rtl_bad.sv \
              $(OTHER_SOURCES)

INC_DIRS = \
	+incdir+$(ROUTER_SRCS) \
	+incdir+$(TXN_SRCS) \
	+incdir+$(ANALYSIS_SRCS) \
	+incdir+$(XACTOR_SRCS) \
	+incdir+$(STIM_SRCS) \
	+incdir+$(ENV_SRCS)

################
# Questa
#

QUESTA_HOME ?= $(dir $(shell which vsim))/..
VSIM_GUI_ARGS = -voptargs="+acc" -classdebug -msgmode both top test
VSIM_ARGS = -t ns +nowarnTSCALE -voptargs="+acc" -c top test -suppress 3829 -do "run -all"
VLOG_ARGS = -incr +acc -suppress 2223 -suppress 2181 +define+ROUTER_SIZE=8

normal: cmp
	vsim  $(VSIM_ARGS)

gui: cmp
	vsim  $(VSIM_GUI_ARGS)

bad: bad_cmp
	vsim  $(VSIM_ARGS)

cmp:
	test -e work || vlib work
	vlog $(VLOG_ARGS) $(SOURCES) $(INC_DIRS) $(DEFINE_FILE_LINE)

bad_cmp:
	test -e work || vlib work
	vlog $(VLOG_ARGS) $(BAD_SOURCES) $(INC_DIRS)

################
# VCS

PLATFORM=$(shell arch)
ifeq "$(PLATFORM)" "x86_64"
VCS =    vcs -full64
else
VCS = vcs
endif

COMMON_VCS = \
	-sverilog -timescale=1ns/1ns \
	+vpi -debug_access+all +define+SNPS \
	+verilog1995ext+.v \
        +define+ROUTER_SIZE=8

SIMV = 	./simv -l vcs.log

vcs:
	$(VCS)  $(COMMON_VCS) $(SOURCES) $(INC_DIRS)
	$(SIMV)

vcs_gui:
	$(VCS)  $(COMMON_VCS) $(SOURCES) $(INC_DIRS) -gui
	$(SIMV)

vcs_bad:
	$(VCS)  $(COMMON_VCS) $(BAD_SOURCES) $(INC_DIRS)
	$(SIMV)

vcs_gui_bad:
	$(VCS)  $(COMMON_VCS) $(BAD_SOURCES) $(INC_DIRS) -gui
	$(SIMV)

################
# CDS

iirun:
	irun -64bit -coverage functional -covoverwrite +define+ROUTER_SIZE=8  $(SOURCES) $(INC_DIRS)

irun_bad:
	irun -64bit -coverage functional -covoverwrite +define+ROUTER_SIZE=8  $(BAD_SOURCES) $(INC_DIRS)

irun_gui:
	irun -64bit -gui -access r -coverage functional -covoverwrite +define+SNPS +define+ROUTER_SIZE=8  $(SOURCES) $(INC_DIRS)

irun_gui_bad:
	irun -64bit -gui -access r -coverage functional -covoverwrite +define+SNPS +define+ROUTER_SIZE=8  $(BAD_SOURCES) $(INC_DIRS)

xrun:
	xrun -64bit -xceligen on -coverage functional -covoverwrite +define+ROUTER_SIZE=8 $(SOURCES) $(INC_DIRS)

xrun_bad:
	xrun -64bit -xceligen on -coverage functional -covoverwrite +define+ROUTER_SIZE=8 $(BAD_SOURCES) $(INC_DIRS)

xrun_gui:
	xrun -64bit -gui -access r  -coverage functional -covoverwrite -xceligen on +define+ROUTER_SIZE=8 $(SOURCES) $(INC_DIRS)

xrun_gui_bad:
	xrun -64bit -gui -access r -coverage functional -covoverwrite -xceligen on +define+ROUTER_SIZE=8 $(BAD_SOURCES) $(INC_DIRS)

################
# Common

clean:
	rm -rf  *.tmp  *.log  log transcript work *.wlf vsim.fcdb *.vstf \
	rm -rf *~ core csrc simv* vc_hdrs.h ucli.key urg* *.log core.*
	rm -rf DVEfiles inter.vpd
	rm -rf xcelium.d xrun.* irun.* cov_work
