module HwMem

import public LinMem
import BitsVec
import LinContext

public export
hw_mem_read: {n: _} -> LinContext (BitsVec n) LinMem -@ LinContext (BitsVec 32) LinMem
hw_mem_read (MkLC addr mem) = let dat # mem' = mem_read addr mem in MkLC dat mem'

public export
hw_mem_write: {n: _} -> LinContext (BitsVec n, BitsVec 32) LinMem -@ LinContext () LinMem
hw_mem_write (MkLC (addr, dat) mem) = MkLC () $ mem_write addr dat mem
