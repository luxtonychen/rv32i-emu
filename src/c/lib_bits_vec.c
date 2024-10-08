#include "./lib_bits_vec.h"


//uint8_t bv_get(uint8_t idx, uint8_t len, uint64_t val) {
uint8_t bv_get(uint8_t idx, BV()) {
  return ((val & MASK(len)) & (1LL << idx)) > 0 ? 1 : 0;
}

/* slice a bit vector in range [lb, ub) */
uint8_t bv_get_range_len(uint8_t lb, uint8_t ub, BV(1)) {
  return ((ub-lb) >= 64) ? 64 : (ub-lb);
}

uint64_t bv_get_range_val(uint8_t lb, uint8_t ub, BV(1)) {
  uint64_t val = EMPTY;
  uint8_t len = ((ub-lb) >= 64) ? 64 : (ub-lb);
  uint8_t i;

  for(i = lb; i < ub; i++){
    if(bv_get(i, bv(1))==1)
      val += (1LL << (i-lb));
  }
  
  return val;
}

//uint8_t bv_sign_ext_len(uint8_t len, uint64_t val) {
uint8_t bv_sign_ext_len(BV()) {
  return 64;
}

uint64_t bv_sign_ext_val(BV()) {
  uint64_t msk = MASK(len);
  uint8_t sign = bv_get(len-1, len, val);
  return ((sign==1) ? ((val & msk) + (FULL ^ msk)) : (val & msk));
}

uint8_t bv_zero_ext_len(BV()) {
  return 64;
}

uint64_t bv_zero_ext_val(BV()) {
  return (val & MASK(len));
}

uint8_t bv_neg_len(BV(1)){
  return len1;
}

uint64_t bv_neg_val(BV(1)){
  uint64_t msk = MASK(len1);
  return ((~val1) & msk);
}

uint8_t bv_and_len(BV(1), BV(2)){
  return MAX(len1, len2);
}

uint64_t bv_and_val(BV(1), BV(2)){
  uint64_t msk = MASK(MAX(len1, len2));
  return (bv_sign_ext_val(bv(1)) & msk)		\
       & (bv_sign_ext_val(bv(2)) & msk);
}

uint8_t bv_or_len(BV(1), BV(2)){
  return MAX(len1, len2);
}

uint64_t bv_or_val(BV(1), BV(2)){
  uint64_t msk = MASK(MAX(len1, len2));
  return (bv_sign_ext_val(bv(1)) & msk)		\
       | (bv_sign_ext_val(bv(2)) & msk);
}

uint8_t bv_xor_len(BV(1), BV(2)){
  return MAX(len1, len2);
}

uint64_t bv_xor_val(BV(1), BV(2)) {
  uint64_t msk = MASK(MAX(len1, len2));
  return (bv_sign_ext_val(bv(1)) & msk)		\
       ^ (bv_sign_ext_val(bv(2)) & msk);
}

uint8_t bv_add_len(BV(1), BV(2)) {
  return MIN(MAX(len1, len2)+1, 64);
}

uint64_t bv_add_val(BV(1), BV(2)) {
  uint64_t msk = MASK(bv_add_len(bv(1), bv(2)));
  return ((bv_sign_ext_val(bv(1)) & (MASK(MAX(len1, len2))))		\
	+ (bv_sign_ext_val(bv(2)) & (MASK(MAX(len1, len2)))))		\
	& msk;
}

uint8_t bv_complement_len(BV()) {
  return len;
}

uint64_t bv_complement_val(BV()) {
  return ((~val) + 1LL) & MASK(len);
}

uint8_t bv_sub_len(BV(1), BV(2)) {
  return bv_add_len(bv(1), bv(2));
}

uint64_t bv_sub_val(BV(1), BV(2)) {
  return bv_add_val(len1, val1, \
		    bv_complement_len(bv(2)),		\
		    bv_complement_val(bv(2)));
}

uint8_t bv_concatenate_len(BV(1), BV(2)) {
  return MIN(len1+len2, 64);
}

uint64_t bv_concatenate_val(BV(1), BV(2)) {
  uint8_t len = bv_concatenate_len(bv(1), bv(2));
  uint64_t msk2 = MASK(len2);
  uint64_t msk1 = MASK(len-len2);

  return ((val1 & msk1) << len2) + (val2 & msk2);
}

uint8_t bv_srl_len(BV(1), BV(2)) {
  return len1;
}

uint64_t bv_srl_val(BV(1), BV(2)) {
  uint8_t sht = (val2) & (MASK8 >> 2) & MASK(len2); //at most lower 6 bits
  return (val1 & MASK(len1)) >> sht;
}

uint8_t bv_sra_len(BV(1), BV(2)) {
  return len1;
}

uint64_t bv_sra_val(BV(1), BV(2)) {
  uint8_t sht = (val2) & (MASK8 >> 2) & MASK(len2); //at most lower 6 bits
  return ((val1 & MASK(len1)) >> sht)					\
    + ((bv_get(len1-1, bv(1))) ? ((FULL << ((len1 > sht) ? len1 - sht : 0)) & MASK(len1)) : EMPTY);
}

uint8_t bv_sll_len(BV(1), BV(2)) {
  return len1;
}

uint64_t bv_sll_val(BV(1), BV(2)) {
  uint8_t sht = (val2) & (MASK8 >> 2) & MASK(len2); //at most lower 6 bits
  return (val1 << sht) & MASK(len1);
}

uint8_t bv_lt_len(BV(1), BV(2)) {
  return 1;
}

uint64_t bv_lt_val(BV(1), BV(2)) {
  uint64_t _val1 = MASK(len1) & val1;
  uint64_t _val2 = MASK(len2) & val2;
  return (((int64_t) bv_sign_ext_val(len1, _val1)) < ((int64_t) bv_sign_ext_val(len2, _val2))) ? 1 : 0;
}

uint8_t bv_eq_len(BV(1), BV(2)) {
  return 1;
}

uint64_t bv_eq_val(BV(1), BV(2)) {
  uint64_t _val1 = MASK(len1) & val1;
  uint64_t _val2 = MASK(len2) & val2;
  return (((int64_t) bv_sign_ext_val(len1, _val1)) == ((int64_t) bv_sign_ext_val(len2, _val2))) ? 1 : 0;
}

uint8_t bv_ltu_len(BV(1), BV(2)) {
  return 1;
}

uint64_t bv_ltu_val(BV(1), BV(2)) {
  return (bv_zero_ext_val(bv(1)) < bv_zero_ext_val(bv(2))) ? 1 : 0;
}

uint64_t bv_get_imm_b(BV()) {
  uint64_t f = ((val & (0x1LL  << 31)) >> 19)	\
             + ((val & (0x1LL  << 7))  << 4)	\
             + ((val & (0x3fLL << 25)) >> 20)	\
             + ((val & (0xfLL  << 8))  >> 7);
  return bv_sign_ext_val(13, (f & 0x1fffLL)) & 0xffffffff;
}

uint64_t bv_get_imm_j(BV()) {
  uint64_t f = ((val & (0x1LL   << 31)) >> 10)	\
             + (val  & (0xffLL  << 12))	        \
             + ((val & (0x1LL   << 20)) >> 9)	\
             + ((val & (0x3ffLL << 21)) >> 20);
  return bv_sign_ext_val(21, (f & 0x1fffffLL)) & 0xffffffff;
}

uint64_t bv_get_imm_s(BV()) {
  uint64_t f = ((val & (0x7fLL << 25)) >> 20)	\
             + ((val & (0x1fLL << 7)) >> 7);
  
  return bv_sign_ext_val(12, (f & 0xfffLL)) & 0xffffffff;
}

void _bv_to_string(BV(1), char* buf) {
  int8_t i = 0;
  int8_t len = (len1 >= 64) ? 64 : len1;
  uint64_t msk = 1;
  
  for(i=0; i<len; i++){
    buf[63-i] = (val1 & msk)>0 ? '1' : '0';
    msk = msk << 1;
  }
  buf[64] = '\0';
}

char* bv_to_string(BV(1)) {
  char buf1[65] = {[0 ... 63] = '-'};
  char buf2[65+15] = {[0 ... 79] = '\0'};
  char* res = malloc(256 * sizeof(char));
  int i, j=0;
  
  _bv_to_string(bv(1), buf1);

  for(i=0; i<64; i++) {
    if ((i % 4 == 0) && (i != 0) && (i != 64)){
      buf2[j] = ' ';
      j++;
    }
    buf2[j] = buf1[i];
    j++;
  }
  
  sprintf(res, "0x%016lx: %02d ", val1, len1);
  strcat(res, buf2);
  return res;
}

void bv_print(BV(1)) {
  char buf[65] = {[0 ... 63] = '-'};
  int i;
  
  _bv_to_string(bv(1), buf);
  
  printf("0x%016lx: %02d ", val1, len1);

  for(i=0; i<64; i++) {
    if ((i % 4 == 0) && (i != 0) && (i != 64))
      putchar(' ');
    putchar(buf[i]);
  }
  puts("\n");
}



