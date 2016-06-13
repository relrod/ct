#!/usr/bin/env bash
echo '-R CT CT ' > _CoqProject ; find . -name '*.v' -print >> _CoqProject
sed -i '/.#.*\.v/d' _CoqProject
make Makefile
