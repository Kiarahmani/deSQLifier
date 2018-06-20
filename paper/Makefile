all:
	pdflatex -shell-escape vldb_sample
	bibtex vldb_sample
	clear
	pdflatex -shell-escape vldb_sample
	clear
	pdflatex -shell-escape vldb_sample

clean:
	rm -f *.log *.aux *.blg *.bbl *.out *~ *.cut
