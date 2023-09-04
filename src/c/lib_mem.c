#include "./lib_bits_vec.h"
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

typedef uint32_t addr_ty;
typedef void*    mem_ty;

mem_ty mem_create(addr_ty len) {
  mem_ty mem = malloc(len * sizeof(uint8_t) + 4);
  mem = memset(mem, 0, len * sizeof(uint8_t) + 4);
  uint8_t i = 0;
  uint8_t sht=0;
  
  for (i=0; i<4; i++){
    ((uint8_t*)mem)[i] = (len >> sht) & ((addr_ty) 0xFF);
    sht += 8;
  }
  return mem;
}

uint8_t mem_read_byte_abs(addr_ty addr, mem_ty mem) {
  addr_ty len = ((addr_ty*) mem)[0];
  if (addr < (len+4))
    return ((uint8_t*) mem)[addr];
  else
    return 0;
}

void mem_write_byte_abs(addr_ty addr, uint8_t val, mem_ty mem) {
  addr_ty len = ((addr_ty*) mem)[0];
  //printf("write abs pos 1 %d\n", addr);
  if (addr < (len+4)){
    //printf("write abs pos 2 %d\n", addr);
    ((uint8_t*) mem)[addr] = val;
  }
}


uint64_t mem_read_32_val(BV(), mem_ty mem) {
  addr_ty addr = ((addr_ty) (val & MASK(32))) + 4;
  uint8_t i;
  uint8_t sht = 0;
  uint64_t ret = 0;
  
  for(i=0; i<4; i++){
    ret +=  ((uint64_t) mem_read_byte_abs(addr+i, mem)) << sht;
    sht += 8;
  }
  return ret;
}

mem_ty mem_write_32(BV(1), BV(2), mem_ty mem) {
  addr_ty addr = ((addr_ty) (val1 & MASK(32))) + 4;
  uint64_t data = val2 & MASK(len2) & MASK(32);
  uint8_t i;
  
  for(i=0; i<4; i++){
    mem_write_byte_abs(addr+i, (uint8_t) (data & MASK8), mem);
    data >>= 8;
  }
  return mem;
}

void mem_diff(mem_ty mem1, mem_ty mem2) {
  addr_ty len = ((addr_ty*) mem1)[0] < ((addr_ty*) mem2)[0] ? ((addr_ty*) mem1)[0] : ((addr_ty*) mem2)[0];
  addr_ty addr;
  uint8_t data1, data2;
  addr_ty count = 0;
  
  for(addr=4; addr<len+4; addr++) {
    data1 = ((uint8_t*)mem1)[addr];
    data2 = ((uint8_t*)mem2)[addr];
    if (data1 != data2) {
      printf("addr: 0x%08x mem1: 0x%02x mem2: 0x%02x\n", addr-4, data1, data2);
      count++;
    }
  }

  if(count == 0){
    printf("No difference detected!\n");
  }
  else{ 
    printf("%d differences detected!\n", count);
  }
}

void mem_free(mem_ty mem) {
  free(mem);
}

mem_ty mem_save(char* fname, mem_ty mem) {
  addr_ty len = ((addr_ty*) mem)[0];
  FILE* f;

  f = fopen(fname, "wb");
  fwrite(mem, len*sizeof(uint8_t)+4, 1, f);
  fclose(f);
  return mem;
}

mem_ty mem_save_2(char* fname, mem_ty mem) {
  addr_ty len = ((addr_ty*) mem)[0];
  FILE* f;

  f = fopen(fname, "wb");
  fwrite(&(((uint8_t*)mem)[4]), len*sizeof(uint8_t), 1, f);
  fclose(f);
  return mem;
}

mem_ty mem_load(char* fname) {
  uint8_t len_buf[4];
  addr_ty len;
  mem_ty mem;
  
  FILE* f = fopen(fname, "rb");
  fread(len_buf, sizeof(len_buf), 1, f);
  len = (addr_ty)len_buf[0] \
      + ((addr_ty)len_buf[1] << 8 )\
      + ((addr_ty)len_buf[2] << 16)\
      + ((addr_ty)len_buf[3] << 24);
  
  mem = malloc(len*sizeof(uint8_t)+4);
  
  for(uint8_t i=0; i<4; i++) {
    ((uint8_t*)mem)[i] = len_buf[i];
  }

  fread(mem+4, len*sizeof(uint8_t), 1, f);
  return mem;
}

mem_ty mem_load_2(char* fname) {
  uint8_t len_buf[4];
  addr_ty len;
  mem_ty mem;
  FILE* f = fopen(fname, "rb");
  uint8_t sht=0;

  fseek(f, 0, SEEK_END); // seek to end of file
  len = ftell(f); // get current file pointer
  fseek(f, 0, SEEK_SET); // seek back to beginning of file
  
  mem = malloc(len*sizeof(uint8_t)+4);
  
  for (uint8_t i=0; i<4; i++){
    ((uint8_t*)mem)[i] = (len >> sht) & ((addr_ty) 0xFF);
    sht += 8;
  }

  fread(mem+4, len*sizeof(uint8_t), 1, f);
  return mem;
}
