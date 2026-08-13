#!/bin/sh
set -xe

coqc PlurimetricFuzz.v
grep -nE '\b(Admitted|admit)\b' *.v
