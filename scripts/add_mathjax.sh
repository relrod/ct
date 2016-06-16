#!/usr/bin/env bash
pushd html
  sed -i '/<\/title>/a\
<script type="text/javascript" async\
  src="https://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-MML-AM_CHTML">\
</script>\
<link href="https://fonts.googleapis.com/css?family=Ubuntu+Mono" rel="stylesheet" type="text/css" />\
<style type="text/css">\
  .code { font-family: "Ubuntu Mono", monospace !important; font-size: 100% !important; }\
</style>\
' *.html
popd
