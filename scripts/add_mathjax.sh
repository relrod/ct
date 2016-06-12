#!/usr/bin/env bash
pushd html
  sed -i '/<\/title>/a\
<script type="text/javascript" async\
  src="https://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-MML-AM_CHTML">\
</script>' *.html
popd