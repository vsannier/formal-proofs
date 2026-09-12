#!/bin/sh
set -xe

coqc PlurimetricFuzz.v

if grep -nE '\b(Admitted|admit)\b' *.v; then
  echo "unfinished proof found" >&2
  exit 1
fi
