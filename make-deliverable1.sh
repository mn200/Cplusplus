cd /tmp
/bin/rm -rf qinetiq-cpp
cvs -d ~/repository export -D "2006-07-03 02:00Z" qinetiq-cpp
cd qinetiq-cpp
cd docs
pdflatex deliverable1-notes
bibtex deliverable1-notes
pdflatex deliverable1-notes
pdflatex deliverable1-notes
/bin/rm deliverable1-notes.{bbl,blg,aux,log}

cd .. ; /bin/rm make-deliverable1.sh

cd talks
latex darp2006
latex darp2006
dvips -Ppdf darp2006
ps2pdf darp2006
rm darp2006.{aux,dvi,log,nav,out,ps,snm,toc} .cvsignore

cd ../..
tar cvzf deliverable1.tgz qinetiq-cpp
