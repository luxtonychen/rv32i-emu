import numpy as np
from hypothesis import given, strategies as st  
from hypothesis import assume
from hypothesis.extra.numpy import arrays as hypothesis_arrays

def mem_read(mem, addr):
    addr_max = len(mem)
    ret = np.uint32(0)
    for i in range(4):
        ret += (mem[addr+i] << (i * 8)) if addr + i < addr_max else 0
    return ret.item()

def mem_write(mem, addr, data):
    addr_max = len(mem)
    for i in range(4):
        if (addr+i) < addr_max:
            mem[addr+i] = (data >> (i*8)) & 0xff

@given(hypothesis_arrays(dtype=np.uint8, 
                         shape=st.integers(min_value=0, max_value=64*1024)), 
       st.integers(min_value=0))
def test_mem_read_elim(mem, rd_addr):
    mem_ = mem.copy()
    mem_read(mem, rd_addr)
    assert mem.shape == mem_.shape
    for i, _ in enumerate(mem):
        assert mem[i] == mem_[i]

@given(hypothesis_arrays(dtype=np.uint8, 
                         shape=st.integers(min_value=0, max_value=64*1024)), 
       st.integers(min_value=0),
       st.integers(min_value=0, max_value=2**32-1))
def test_mem_write_elim1(mem, wt_addr, wt_data):
    assume(wt_addr+3 < len(mem))
    mem_write(mem, wt_addr, wt_data)
    assert mem_read(mem, wt_addr) == wt_data

@given(hypothesis_arrays(dtype=np.uint8, 
                         shape=st.integers(min_value=0, max_value=64*1024)), 
       st.integers(min_value=0),
       st.integers(min_value=0, max_value=2**32-1),
       st.integers(min_value=0, max_value=2**32-1))
def test_mem_write_elim2(mem, wt_addr, wt_data1, wt_data2):
    assume(wt_addr+3 < len(mem))
    mem_write(mem, wt_addr, wt_data1)
    mem_write(mem, wt_addr, wt_data2)
    assert mem_read(mem, wt_addr) == wt_data2
    