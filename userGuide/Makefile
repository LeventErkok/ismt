TARGET   = ismtUserGuide
SRCS     = ${TARGET}.tex ${TARGET}.bib
AUX      = ${wildcard *.blg} ${wildcard *.bbl} ${wildcard *.aux} \
           ${wildcard *.eps} ${wildcard *.log} ${wildcard *.toc} \

all: pdf

pdf: ${TARGET}.pdf

${TARGET}.pdf: ${SRCS} Makefile
	pdflatex ${TARGET}
	bibtex ${TARGET}
	pdflatex ${TARGET}
	pdflatex ${TARGET}

clean:
	rm -f ${AUX}

superClean: clean
	rm -f  *.pdf 
