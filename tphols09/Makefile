WORK=latex_files
REFS=tphols09.bib
TGT=tphols09

.PHONY: clean

$(TGT).pdf $(WORK)/$(TGT).aux: $(WORK) $(WORK)/$(TGT).bbl $(TGT).tex
	pdflatex --output-directory $(WORK) $(TGT).tex


$(WORK)/$(TGT).bbl : $(REFS) $(WORK)/$(TGT).aux
	bibtex $(WORK)/$(TGT).aux
	pdflatex --output-directory $(WORK) $(TGT).tex


$(WORK):
	mkdir -p $(WORK)

clean:
	-rm -rf $(WORK)
