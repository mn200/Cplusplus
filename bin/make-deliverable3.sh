tgt=deliverable3
localdir=~/nicta/projects/cpp-project/deliverables
cd /tmp
/bin/rm -rf qinetiq-cpp
svn export file:///home/users/michaeln/nicta/projects/cpp-project/qcpp-repos/deliverables/$tgt qinetiq-cpp
cd qinetiq-cpp
cd docs
atex $tgt-notes
bibtex $tgt-notes
latex $tgt-notes
latex $tgt-notes
mdvips $tgt-notes
/bin/rm $tgt-notes.{bbl,blg,aux,log} cpp-macros.aux

cd .. ; /bin/rm -r bin

cd talks
latex darp2006
latex darp2006
mdvips  darp2006
rm darp2006.{aux,dvi,log,nav,out,ps,snm,toc}

cd ../..
mv -i qinetiq-cpp/docs/$tgt-notes.pdf $localdir
tar cvzf $tgt.tgz qinetiq-cpp
mv -i $tgt.tgz $localdir

