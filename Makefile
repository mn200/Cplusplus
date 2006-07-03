deliverable1:
	cd /tmp ; /bin/rm -rf qinetiq-cpp \
        cvs -d ~/repository export -D "2006-07-03 01:47Z" qinetiq-cpp ; \
        cd qinetiq-cpp ;\
	cd docs ; pdflatex deliverable1-notes ; bibtex deliverable1-notes ;\
        pdflatex deliverable1-notes ;\
        pdflatex deliverable1-notes ;\
	/bin/rm deliverable1-notes.{bbl,blg,aux,log} ;\
        cd .. ; /bin/rm Makefile ;\
        cd .. ; tar cvzf deliverable1.tgz qinetiq-cpp
