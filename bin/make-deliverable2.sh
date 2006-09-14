tgt=deliverable2
localdir=~/nicta/projects/cpp-project/deliverables
cd /tmp
/bin/rm -rf qinetiq-cpp
svn export file:///home/users/michaeln/nicta/projects/cpp-project/qcpp-repos/tags/deliverable-2 qinetiq-cpp
cd qinetiq-cpp
cd docs
pdflatex $tgt-notes
bibtex $tgt-notes
pdflatex $tgt-notes
pdflatex $tgt-notes
/bin/rm $tgt-notes.{bbl,blg,aux,log} cpp-macros.aux

cd .. ; /bin/rm -r bin

cd talks
latex darp2006
latex darp2006
dvips -Ppdf darp2006
ps2pdf14 darp2006.ps
rm darp2006.{aux,dvi,log,nav,out,ps,snm,toc}

cd ../..
mv -i qinetiq-cpp/docs/$tgt-notes.pdf $localdir
tar cvzf $tgt.tgz qinetiq-cpp
mv -i $tgt.tgz $localdir

