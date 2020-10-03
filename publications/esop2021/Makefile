SYSTEM := dependent-subtyping
SYSTEM_OTT := ../../formalisation/Declarative/src/ott/Language.ott

PAPER := main
SECTIONS_DIR := sections
SECTIONS := ${wildcard ${SECTIONS_DIR}/*.tex}

OTT := ott

${PAPER}.pdf : ${PAPER}.tex ${SECTIONS:${SECTIONS_DIR}/%.tex=%.filt.tex} ${SYSTEM}.ott.tex
	latexmk -dvi- -pdf $<
	@latexmk -c

${SYSTEM}.ott.tex : ${SYSTEM}.dump
	${OTT} -readsys $^ -o $@ -tex_wrap false

${SYSTEM}.dump : ${SYSTEM_OTT}
	${OTT} $< -writesys $@

%.filt.tex : ${SECTIONS_DIR}/%.tex ${SYSTEM}.dump
	${OTT} -readsys ${SYSTEM}.dump -tex_filter $< $@

.PHONY: ott clean

ott : ${SYSTEM}.ott.tex ${PAPER}.tex

clean :
	latexmk -C
	rm ${SYSTEM}.dump *.filt.tex