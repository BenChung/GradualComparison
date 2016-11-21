all: figures
	pdflatex main.tex
	bibtex main

siek:
	pdflatex siek-mod && open siek-mod.pdf

no:
	bibtex main
	pdflatex main.tex

jan: 
	pdflatex common && open common.pdf

halfclean:
	rm -f *.log *.aux *.bbl *.blg *~  *.out  *#  .#*  *.fls

clean: halfclean
	rm -f main.pdf

figures:
	racket format-racket.rkt ../examples/typed_racket/untyped1.rkt untyped-rkt1.pdf
	racket format-racket.rkt ../examples/typed_racket/typed1.rkt typed-rkt1.pdf
	racket format-racket.rkt ../examples/typed_racket/typed2.rkt typed-rkt2.pdf
