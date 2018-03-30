all:
	pdflatex -shell-escape main
	bibtex main
	pdflatex -shell-escape main
	pdflatex -shell-escape main

clean:
	rm -f *.log *.aux *.blg *.bbl *.out *~ *.cut
