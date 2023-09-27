#!/bin/bash

FILES="./bin/*.bin"

for f in $FILES
do
    ../src/idris/build/exec/rv32i "$f" $1
done
