module
public import LeanFloats.ForMathlib

open Float.Model

@[expose]
public def Float.Model.Format.infinityExponent (f : Format) : Nat :=
  2 ^ (f.exponentBits - 1)

namespace LeanFloats.UnpackedFloat

scoped macro "format_trivial" : tactic =>
  `(tactic| (
    simp +zetaDelta [Format.exponentBias, Format.infinityExponent, Format.minExponent,
      Format.exponentBias, Format.mantissaBits, Format.numBits, totalExponent,
      Format.targetExponent, Nat.log2_two_pow_add, Nat.log2_two_pow, BitVec.isLt,
      $(Lean.mkCIdent `LeanFloats.UnpackedFloat.CommonFormat.toFormat):ident] at *
    first
    | lia
    | grind [= Nat.log2_two_pow, Format.hm, Format.he]
  ))

end LeanFloats.UnpackedFloat
