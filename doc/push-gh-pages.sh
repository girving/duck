#!/usr/bin/zsh -e

setopt cshnullglob

cd ${0:h}
files=(*.textile *.markup *.html)
rev=$(git rev-list HEAD --max-count=1 -- $files)
ref=$(git symbolic-ref HEAD)

cd ..
dir=`mktemp -d ./tmp.gh-pages.XXXXXX`
for f in $files ; do
        echo $f
	title=$(sed -n '0,/^\(h1.\|#\) \+\(.*\)$/s//\2/p' doc/$f)
	exec 3> $dir/$f
	echo "---" >&3
	echo "title: $title" >&3
	echo "---" >&3
	cat doc/$f >&3
	exec 3>&-
done

git checkout gh-pages
mv $dir/* .
rm -rf $dir
git add $files
git status
git commit -C $rev
git push origin gh-pages
git checkout ${ref#refs/heads/}
