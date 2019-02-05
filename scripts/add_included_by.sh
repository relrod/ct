#!/usr/bin/env bash

tmpdir=`mktemp -d`

pushd CT
  for d in `find -type d -print | tail -n +2`; do
    for f in `find "$d" -name '*.v'`; do
      ( #grep "(* This file is auto-generated. *)" "$f" && continue
        module="$(echo "$f" | sed 's/^\.\///' | sed 's/\//./g' | sed 's/\.v$//')"
        line="$(grep -E "Require (Import|Export)" "$f" | sed 's/\.$//' | sed 's/Require (Import|Export) //')"
        set -f
        for i in ${line}; do
          set +f
          echo "<li><a href=\"CT.$module.html\">CT.$module<\/a><\/li>" >> "$tmpdir/$i"
        done ) &
    done
  done
popd

wait

pushd html
  for f in `find -name '*.html'`; do
    (
    docmodule="$(basename "$f" | sed 's/^\.\///' | sed 's/\//./g' | sed 's/\.html$//')"
    tmpf="$tmpdir/$docmodule"
    echo "Matching $docmodule"

    [[ ! -f "$tmpf" ]] && continue

    sort -o "$tmpf" "$tmpf"
    uniq "$tmpf" "$tmpf.uniq"
    mv "$tmpf.uniq" "$tmpf"

    echo "Inserting matches"
    sed -i "s/<div id=\"footer\">/<div id=\"footer\" style=\"padding: 10px;\"><p>This module is included by:<\/p><ul>$(cat "$tmpf"|tr '\n' ' ')<\/ul>/" $f
    ) &
  done
popd

wait

rm -rfv "$tmpdir"
