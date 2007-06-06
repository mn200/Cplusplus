final-deliverable: 
	latex $@
	latex $@
	bibtex $@
	makeindex $@
	latex $@
	latex $@
	dvips -Ppdf $@ -o temp.ps
	mv temp.ps final-deliverable.ps
	ps2pdf final-deliverable.ps
