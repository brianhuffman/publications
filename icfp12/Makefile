WORK=latex_files
REFS=root.bib

DEPS = \
  root.bib \
  sigplanconf.cls \
  mathpartir.sty

.PHONY: clean

root.pdf $(WORK)/root.aux: $(WORK) $(WORK)/root.bbl root.tex $(DEPS)
	pdflatex --output-directory $(WORK) root.tex


$(WORK)/root.bbl : $(REFS) $(WORK)/root.aux
	bibtex $(WORK)/root.aux
	pdflatex --output-directory $(WORK) root.tex

abstract.pdf $(WORK)/abstract.aux: $(WORK) $(WORK)/abstract.bbl abstract.tex $(DEPS)
	pdflatex --output-directory $(WORK) abstract.tex


$(WORK)/abstract.bbl : $(REFS) $(WORK)/abstract.aux
	bibtex $(WORK)/abstract.aux
	pdflatex --output-directory $(WORK) abstract.tex

$(WORK):
	mkdir -p $(WORK)

clean:
	-rm -rf $(WORK)
