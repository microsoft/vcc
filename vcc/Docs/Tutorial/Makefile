-include Makefile.local

PAPER_BASE = vcc-tutorial-col
COLUMNS ?= 1w
PAPER = $(PAPER_BASE)$(COLUMNS)
BIB = tutorial.bib 
OTHERSOURCES := $(wildcard *.tex) $(wildcard c/*.c)

all: $(PAPER).pdf

.PHONY: pdf
pdf: $(PAPER).pdf

$(PAPER).bbl: $(PAPER).aux $(BIB)
	bibtex $(PAPER)

$(PAPER).aux:
	pdflatex $(PAPER).tex </dev/null


$(PAPER).pdf: $(PAPER).bbl $(PAPER).tex $(OTHERSOURCES)
	echo "Rerun to get cross" >> $(PAPER).log
	while grep -q "Rerun to get cross" $(PAPER).log; do \
		if pdflatex $(PAPER).tex </dev/null; then \
			true; \
		else \
			stat=$$?; touch $(PAPER).pdf; exit $$stat; \
		fi; \
	done
	touch $(PAPER).bbl
	touch $(PAPER).pdf
	cp $(PAPER).pdf view.pdf


$(PAPER).ps: $(PAPER).pdf
	pdf2ps $(PAPER).pdf

clean:
	rm -f *.aux *.log $(PAPER_BASE)*.ps *.dvi *.blg *.bbl *.toc *~ *.out $(PAPER_BASE)*.pdf view.pdf


both:
	$(MAKE) COLUMNS=1
	$(MAKE) COLUMNS=2
	$(MAKE) COLUMNS=1w

send: both
	$(WEBCP) $(PAPER_BASE){1,2}.pdf 
