CC      = riscv32-unknown-elf-gcc
OBJCPY  = riscv32-unknown-elf-objcopy
DIR_SRC = ./src
DIR_OBJ = ./bin
SRCS    = $(foreach f, $(wildcard $(DIR_SRC)/*.S), $(notdir $(f)))
OBJS    = $(addprefix $(DIR_OBJ)/, $(SRCS:S=o))

.PHONY: clean

all: $(OBJS)

$(DIR_OBJ)/%.o: $(DIR_SRC)/%.S
	$(CC) -nostdlib -nostartfiles -T ./env/link.ld -o $@ $^
	$(OBJCPY) -O binary $@ $(@:o=bin)

clean:
	rm -rf $(DIR_OBJ)/*.o
	rm -rf $(DIR_OBJ)/*.bin


