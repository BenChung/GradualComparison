all:
	pdflatex main.tex

no:
	bibtex main
	pdflatex main.tex

jan:
	pdflatex main; open main.pdf

halfclean:
	rm -f *.log *.aux *.bbl *.blg *~

clean: halfclean
	rm -f main.pdf

