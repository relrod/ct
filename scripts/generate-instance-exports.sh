#!/usr/bin/env bash
set -e
pushd CT/Instance
  grep -l '\(\* This file is auto-generated. \*\)' . -R | xargs rm -v
  for d in `find -type d -print | tail -n +2`; do
    coqfile="$(echo "$d" | sed 's/^\.\///').v"
    [ -f "$coqfile" ] && rm "$coqfile"
    echo "(* This file is auto-generated. *)" > "$coqfile"
    for f in `find "$d" -name '*.v'`; do
      module="$(echo "$f" | sed 's/^\.\///' | sed 's/\//./g' | sed 's/\.v$//')"
      echo "Require Export CT.Instance.$module." >> "$coqfile"
    done
    echo "Sorting $coqfile"
    sort -o "$coqfile" "$coqfile"
  done
popd
