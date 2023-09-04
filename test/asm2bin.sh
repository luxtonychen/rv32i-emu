#!/bin/bash

FILES="./src/*.S"

for f in $( eval basename -s .S $FILES)
do
	riscv32-unknown-elf-gcc -nostdlib -nostartfiles -T ./env/link.ld -o ./bin/$f.o ./src/$f.S 
	riscv32-unknown-elf-objcopy -O binary ./bin/$f.o ./bin/$f.bin
done
