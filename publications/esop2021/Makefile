SYSTEM := dependent-subtyping
SYSTEM_OTT := ../../formalisation/Declarative/src/ott/Language.ott

PAPER := main

OTT := ott

${PAPER}.pdf : ${PAPER}.tex ${SYSTEM}.ott.tex
	latexmk -dvi- -pdf $<
	latexmk -c

${SYSTEM}.ott.tex : ${SYSTEM}.dump
	${OTT} -readsys $^ -o $@ -tex_wrap false

${SYSTEM}.dump : ${SYSTEM_OTT}
	${OTT} $< -writesys $@

${PAPER}.tex : ${PAPER}.src.tex ${SYSTEM}.dump
	${OTT} -readsys ${SYSTEM}.dump -tex_filter ${PAPER}.src.tex $@

.PHONY: ott clean

ott : ${SYSTEM}.ott.tex ${PAPER}.tex

clean :
	latexmk -C
	rm ${PAPER}.tex ${SYSTEM}.dump ${SYSTEM}.ott.tex