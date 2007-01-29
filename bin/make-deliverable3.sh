tgt=deliverable3
localdir=~/nicta/projects/cpp-project/deliverables
cd /tmp
/bin/rm -rf qinetiq-cpp
svn export file:///home/users/michaeln/nicta/projects/cpp-project/qcpp-repos/deliverables/$tgt qinetiq-cpp
cd qinetiq-cpp
cd docs
latex $tgt-notes
bibtex $tgt-notes
latex $tgt-notes
latex $tgt-notes
mdvips $tgt-notes
/bin/rm $tgt-notes.{bbl,blg,aux,log} cpp-macros.aux

cd .. ; /bin/rm -r bin

cd ../
mv -i qinetiq-cpp/docs/$tgt-notes.pdf $localdir
tar cvzf $tgt.tgz qinetiq-cpp
mv -i $tgt.tgz $localdir

