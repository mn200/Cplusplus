cd /tmp
/bin/rm -rf qinetiq-cpp
svn export file:///home/users/michaeln/nicta/projects/cpp-project/qcpp-repos/tags/deliverable-1 qinetiq-cpp
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
ps2pdf14 darp2006.ps
rm darp2006.{aux,dvi,log,nav,out,ps,snm,toc} .cvsignore

cd ../..
tar cvzf deliverable1.tgz qinetiq-cpp
mv -i deliverable1.tgz ~/nicta/projects/cpp-project

