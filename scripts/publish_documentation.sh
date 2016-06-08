#!/usr/bin/env bash
set -e
dir="$(mktemp -d)"
git clone git@github.com:relrod/ct $dir/repo
pushd $dir/repo
./scripts/generate_CoqProject.sh
make -j4 html
mv html ..
make clean
git reset --hard
git checkout gh-pages
mv ../html/* .
git add .
git commit -m 'documentation deploy'
git push origin gh-pages
popd
rm -rf "$dir"
