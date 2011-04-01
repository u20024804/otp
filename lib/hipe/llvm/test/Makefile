#
# Makefile for tests
#

ESRC = .
EBIN = .
ERLC = erlc
PWD = $(shell pwd)
APPDIR = $(shell dirname $(PWD))
ERL_COMPILE_FLAGS = -pa $(APPDIR)/ebin

Mods = math_test \
	   tuple_test

ErlSrc          = $(Mods:%=%.erl)
ErlTargets      = $(Mods:%=$(EBIN)/%.beam) 
RtlFiles        = *.rtl
LlvmFiles       = *.ll

# Targets
opt debug: $(ErlTargets)

clean: 
	rm -f $(ErlTargets)
	rm -f $(RtlFiles) $(LlvmFiles)
	rm -f *~ 

# Rules
ifneq ($(INSIDE_ERLSRC),true)

$(EBIN)/%.beam: $(ESRC)/%.erl
	$(ERLC) -W -bbeam $(ERL_FLAGS) $(ERL_COMPILE_FLAGS) -o$(EBIN) $<
endif
# EOF
