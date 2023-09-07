#ifndef LIB_BITS_VEC
#define LIB_BITS_VEC

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define FULL      0xFFFFFFFFFFFFFFFF
#define EMPTY     0x0000000000000000
#define MASK8     0xFFLL
#define MASK16    0xFFFFLL
#define MASK(LEN) (FULL >> (64 - LEN))
#define MAX(A, B) (A > B? A : B)
#define MIN(A, B) (A < B? A : B)


#define BV(N) uint8_t len ## N, uint64_t val ## N
#define bv(N) len ## N, val ## N

uint8_t bv_get(uint8_t idx, BV());

uint8_t bv_get_range_len(uint8_t lb, uint8_t ub, BV());

uint64_t bv_get_range_val(uint8_t lb, uint8_t ub, BV());

uint8_t bv_sign_ext_len(BV());

uint64_t bv_sign_ext_val(BV());

uint8_t bv_zero_ext_len(BV());

uint64_t bv_zero_ext_val(BV());

uint8_t bv_and_len(BV(1), BV(2));

uint64_t bv_and_val(BV(1), BV(2));

uint8_t bv_or_len(BV(1), BV(2));

uint64_t bv_or_val(BV(1), BV(2));

uint8_t bv_xor_len(BV(1), BV(2));

uint64_t bv_xor_val(BV(1), BV(2));

uint8_t bv_add_len(BV(1), BV(2));

uint64_t bv_add_val(BV(1), BV(2));

uint8_t bv_complement_len(BV());

uint64_t bv_complement_val(BV());

uint8_t bv_sub_len(BV(1), BV(2));

uint64_t bv_sub_val(BV(1), BV(2));

uint8_t bv_concatenate_len(BV(1), BV(2));

uint64_t bv_concatenate_val(BV(1), BV(2));

uint8_t bv_srl_len(BV(1), BV(2));

uint64_t bv_srl_val(BV(1), BV(2));

uint8_t bv_sra_len(BV(1), BV(2));

uint64_t bv_sra_val(BV(1), BV(2));

uint8_t bv_sll_len(BV(1), BV(2));

uint64_t bv_sll_val(BV(1), BV(2));

uint8_t bv_lt_len(BV(1), BV(2));

uint64_t bv_lt_val(BV(1), BV(2));

uint8_t bv_ltu_len(BV(1), BV(2));

uint64_t bv_ltu_val(BV(1), BV(2));

void _bv_to_string(BV(1), char* buf);

void bv_print(BV(1));

#endif
