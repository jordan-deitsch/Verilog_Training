SHELL = /bin/sh

PLATFORM=$(shell uname -s)
ifeq "$(PLATFORM)" "SunOS"
TARGET_ARCH = gccsparcOS5
endif
ifeq "$(PLATFORM)" "Linux"
TARGET_ARCH = linux
endif
ifeq "$(PLATFORM)" "CYGWIN_NT-5.0"
TARGET_ARCH = cygwin
endif
ifeq "$(PLATFORM)" "CYGWIN_NT-5.1"
TARGET_ARCH = cygwin
endif

ifndef TARGET_ARCH
  $(error These labs are only supported on Linux or SunOS. I do not recognize platform $(PLATFORM))
endif



all:
	@echo "This makefile provides the following  targets:"
	@echo "    distclean               Removes all non-essential files"
	@echo "                            from this lab directory."
	@echo ""
	@echo "    tarball                 First does a distclean, then creates"
	@echo "                            a gzipped tar file in /tmp/$(USER)_labs.tar.gz"

distclean:
	@echo "Cleaning up files..."
	find . -name '*.vcd' -exec rm -f {} \; ; \
	find . -name 'core' -exec rm -f {} \; ; \
	find . -name '.cwr*' -exec rm -f {} \; ; \
	find . -name 'transcript' -exec rm -f {} \; ; \
	find . -name 'work*' -exec rm -rf {} \; ; \
	find . -name 'vsim*' -exec rm -f {} \; ; \
	find . -name 'simv*' -exec rm -rf {} \; ; \
	find . -name 'vc_hdrs.h' -exec rm -rf {} \; ; \
	find . -name 'assert.report' -exec rm -f {} \; ; \
	find . -name 'csrc' -exec rm -rf {} \; ; \
	find . -name '*.log' -exec rm -f {} \; ; \
	find . -name '*.so' -exec rm -f {} \; ; \
	find . -name '*.vstf' -exec rm -f {} \; ; \
	find . -name '*DVEfiles' -exec rm -f {} \; ; \
	find . -name '*.vpd' -exec rm -f {} \; ; \
	find . -name '*.key' -exec rm -f {} \; ; \
	find . -name '*.tcl' -exec rm -f {} \; ; \
	find . -name '*.old' -exec rm -f {} \; ; \
	find . -name 'INCA_libs' -exec rm -rf {} \; ; \
	find . -name 'xcelium.d' -exec rm -rf {} \; ; \
	find . -name 'irun.*' -exec rm -rf {} \; ; \
	find . -name 'xrun.*' -exec rm -rf {} \; ; \
	find . -name 'cov_work' -exec rm -rf {} \; ; \
	rm -rf sim ; \
	rm -rf .test

tarball: distclean
	@rm -f /tmp/$(USER)_labs.tar ; \
	rm -f /tmp/$(USER)_labs.tar.gz ; \
	tar -cf /tmp/$(USER)_labs.tar * ; \
	gzip /tmp/$(USER)_labs.tar ; \
	echo "The lab files are in /tmp/$(USER)_labs.tar.gz" ; \
	echo "To install, create a new directory and unzip/untar this file into that directory."


