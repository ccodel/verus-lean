/-

Basic facts and definitions on fixed-width integers.

Authors: the Verus-Lean contributors.

-/

set_option hygiene false in
macro "declare_uint_bnot" typeName:ident : command =>
`(
namespace $typeName

def bnot (x : $typeName) : $typeName :=
  if x = (0 : $typeName) then (1 : $typeName) else (0 : $typeName)

prefix:100 "!" => bnot

end $typeName
)

declare_uint_bnot UInt8
declare_uint_bnot UInt16
declare_uint_bnot UInt32
declare_uint_bnot UInt64
declare_uint_bnot USize
