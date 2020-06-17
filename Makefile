PROJECT := DependentInference

COQ_PROJECT  := _CoqProject
COQ_MAKE     := coq_makefile
COQ_MAKEFILE := CoqMakefile

OTT_SOURCES  := Declarative/Language.ott
OTT_COQ_OUTS := Declarative/Language.v

COQ_SOURCES := $(shell \
	find . -name *.v   \
		$(foreach o,$(notdir ${OTT_COQ_OUTS}),-not -name ${o}))

${COQ_PROJECT} : ${OTT_COQ_OUTS} ${COQ_SOURCES}
	@echo "MAKE: Generating _CoqProject"
	@echo "# Generated by Makefile" > $@
	@echo -R . ${PROJECT}           > $@
	@$(foreach f,$^,echo ${f}      >> $@;)

${OTT_COQ_OUTS} : ${OTT_SOURCES}
	@echo "MAKE: Generating rules for coq by ott"
	@ott -o $@ $^

${COQ_MAKEFILE} : ${COQ_PROJECT} ${COQ_SOURCES} ${OTT_COQ_OUTS}
	@echo MAKE: Generating ${COQ_MAKEFILE}
	@${COQ_MAKE} -f ${COQ_PROJECT} -o $@

.PHONY: ott coq clean

ott: ${OTT_COQ_OUTS}

coq: ott ${COQ_MAKEFILE}
	@echo "MAKE: Compiling coq sources"
	@${MAKE} -f ${COQ_MAKEFILE}

clean:
	@echo "MAKE: Cleaning all generated files"
	@${MAKE} -f ${COQ_MAKEFILE} clean > /dev/null
	@rm ${COQ_PROJECT} ${OTT_COQ_OUTS}
