all: figures
	pdflatex gradualcomp
	bibtex gradualcomp
	pdflatex gradualcomp
	pdflatex gradualcomp

jan: 
	pdflatex gradualcomp && open gradualcomp.pdf

halfclean:
	rm -f *.log *.aux *.bbl *.blg *~  *.out  *#  .#*  *.fls *.vtc

clean: halfclean
	rm -f gradualcomp.pdf

# figures:
# 	racket format-racket.rkt ../examples/typed_racket/untyped1.rkt untyped-rkt1.pdf
# 	racket format-racket.rkt ../examples/typed_racket/typed1.rkt typed-rkt1.pdf
# 	racket format-racket.rkt ../examples/typed_racket/typed2.rkt typed-rkt2.pdf
