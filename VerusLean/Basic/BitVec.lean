/-

Basic facts and definitions on parameterized fixed-width bitvectors.

Authors: the Verus-Lean contributors.

-/

namespace BitVec

def bnot (x : BitVec n) : BitVec n :=
  if x = 0 then 1 else 0

prefix:100 "!" => bnot

end BitVec
