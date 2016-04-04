all: 
	pdflatex main.tex
	bibtex main

siek:
	pdflatex siek-mod && open siek-mod.pdf

no:
	bibtex main
	pdflatex main.tex

jan:
	pdflatex main && open main.pdf

halfclean:
	rm -f *.log *.aux *.bbl *.blg *~  *.out  *#  .#*  *.fls

clean: halfclean
	rm -f main.pdf

