#include "./lib_bits_vec.h"
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

typedef uint32_t addr_ty;
typedef void*    mem_ty;

// require -wp-model Typed+Cast
/*@ assigns \nothing;
    ensures \forall integer i; 
            \valid_read((uint8_t*)mem + i) 
            ==> ((uint8_t*)mem)[i] == \old(((uint8_t*)mem)[i]);
*/
uint8_t mem_read_byte_abs(addr_ty addr, mem_ty mem) {
  addr_ty len = ((addr_ty*) mem)[0];
  if (addr < (len+4))
    return ((uint8_t*) mem)[addr];
  else
    return 0;
}

// require -wp-model Typed+Cast
/*@ assigns \nothing;
    ensures \forall integer i; 
            \valid_read((uint8_t*)mem + i) 
            ==> ((uint8_t*)mem)[i] == \old(((uint8_t*)mem)[i]);
*/
uint64_t mem_read_32_val(BV(), mem_ty mem) {
  addr_ty addr = ((addr_ty) (val & MASK(32))) + 4;
  uint8_t i;
  uint8_t sht = 0;
  uint64_t ret = 0;
  
  /*@ loop assigns i, ret, sht;
      loop invariant i <= 4;
      loop variant 4-i;
  */
  for(i=0; i<4; i++){
    ret +=  ((uint64_t) mem_read_byte_abs(addr+i, mem)) << sht;
    sht += 8;
  }
  return ret;
}

