#Makefile for wishbone memory


################
# WISHBONE directories
WISHBONE_BUS      = ./wishbone_bus
WISHBONE_MEM      = ./wishbone_mem

################
# Sub directories

ANALYSIS_SRCS  = ./analysis
ENV_SRCS       = ./env
TOP_SRCS       = ./top_modules

################
# Sources to compile

COMMON_SOURCES = \
        $(TOP_SRCS)/test_params_pkg.sv \
        $(WISHBONE_BUS)/wishbone_pkg.sv \
        $(ANALYSIS_SRCS)/analysis_pkg.sv \
        $(ENV_SRCS)/env_pkg.sv \
        $(WISHBONE_BUS)/wb_reset_if.sv \
        $(WISHBONE_BUS)/wb_syscon_bfm_if.sv \
        $(TOP_SRCS)/top.sv \
        $(TOP_SRCS)/test.sv

SOURCES =  \
	$(WISHBONE_MEM)/wb_slave_mem.sv \
	$(COMMON_SOURCES) \

BAD_SOURCES = \
	$(WISHBONE_MEM)/wb_slave_mem_bad.sv \
	$(COMMON_SOURCES)


INC_DIRS = \
	+incdir+$(WISHBONE_MEM) \
	+incdir+$(ANALYSIS_SRCS) \
	+incdir+$(WISHBONE_BUS) \
	+incdir+$(ENV_SRCS) \

################
# Questa
QUESTA_HOME ?= $(dir $(shell which vsim))/..
VSIM_GUI_ARGS = -voptargs="+acc" -classdebug -msgmode both
VSIM_ARGS = -t ns +nowarnTSCALE -voptargs="+acc" -c top test -suppress 3829 -do "run -all"
VLOG_ARGS = -incr +acc -O0 -suppress 2223 -suppress 2181

normal: cmp
	vsim $(VSIM_ARGS)
gui: cmp
	vsim $(VERBOSITY) $(VSIM_GUI_ARGS) top test

cmp:
	test -e work || vlib work
	vlog $(VLOG_ARGS) $(INC_DIRS) $(SOURCES)  $(DEFINE_FILE_LINE)
bad: bad_cmp
	vsim $(VSIM_ARGS) $(VERBOSITY)

bad_gui: bad_cmp
	vsim $(VERBOSITY) $(VSIM_GUI_ARGS) top test

bad_cmp:
	test -e work || vlib work
	vlog $(VLOG_ARGS) $(INC_DIRS) $(BAD_SOURCES)  $(DEFINE_FILE_LINE)

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
	$(VCS) $(COMMON_VCS) $(SOURCES) $(INC_DIRS)
	$(SIMV)

vcs_gui:
	$(VCS) $(COMMON_VCS) $(SOURCES) $(INC_DIRS) -gui
	$(SIMV)

vcs_bad:
	$(VCS) $(COMMON_VCS) $(BAD_SOURCES) $(INC_DIRS)
	$(SIMV)

vcs_gui_bad:
	$(VCS) $(COMMON_VCS) $(BAD_SOURCES) $(INC_DIRS) -gui
	$(SIMV)

################
# Cadence

irun:
	irun -64bit  $(SOURCES) $(INC_DIRS)

irun_bad:
	irun -64bit $(BAD_SOURCES)  $(INC_DIRS)

irun_gui:
	irun -64bit -gui -access r  $(SOURCES)  $(INC_DIRS)

irun_gui_bad:
	irun -64bit -gui -access r  $(BAD_SOURCES)  $(INC_DIRS)

xrun:
	xrun -64bit -xceligen on $(SOURCES) $(INC_DIRS)

xrun_bad:
	xrun -64bit -xceligen on $(BAD_SOURCES) $(INC_DIRS)

xrun_gui:
	xrun -64bit -gui -access r  -xceligen on $(SOURCES) $(INC_DIRS)

xrun_gui_bad:
	xrun -64bit -gui -access r -xceligen on $(BAD_SOURCES) $(INC_DIRS)



################
# Common

clean:
	rm -rf  *.tmp  *.log  log transcript work *.wlf vsim.fcdb *.vstf \
	rm -rf *~ core csrc simv* vc_hdrs.h ucli.key urg* *.log core.*
	rm -rf DVEfiles inter.vpd
	rm -rf xcelium.d xrun.* irun.*
