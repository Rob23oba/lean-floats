module
public import LeanFloats.UnpackedFloat.Basic
public import LeanFloats.PackLemmas

@[expose] public section

namespace LeanFloats.UnpackedFloat

open Float.Model
open LeanFloats.UnpackedFloat

@[simp]
lemma CommonFormat.infinityExponent_toFormat (f : CommonFormat) :
    f.toFormat.infinityExponent = f.toFloatFormat.infExp := by
  simp [Float.Model.Format.infinityExponent]

inductive IsValid (fmt : Format) : UnpackedFloat → Prop where
  | notANumber : IsValid fmt .notANumber
  | infinity {s} : IsValid fmt (.infinity s)
  | zero {s} : IsValid fmt (.zero s)
  | finite {s m e} (hm) (hmant : e = fmt.targetExponent (totalExponent m e))
    (he : e ≤ fmt.infinityExponent - fmt.mantissaBits) :
    IsValid fmt (.finite s m e hm)

variable {fmt : CommonFormat}

@[simp]
lemma isValid_toUnpackedFloat (x : RealFloat fmt.toFloatFormat) :
    IsValid fmt.toFormat (toUnpackedFloat x) := by
  fun_cases toUnpackedFloat
  · constructor
  · rename_i s x h hx
    constructor
    · rw [← getExponent_eq_targetExponent (f := 0) _ (by simp) (by simp)]
      · congr 1; symm
        simpa using h.isRounded.abs_getMantissa_mul_base_pow_getExponent
      · simp [h.isRounded.getMantissa_eq_zero_iff, hx]
    · simpa using h.inRange.getExponent_le
  · constructor
  · constructor

lemma isValidFloat_of_isValid_finite {s m e hm}
    (h : IsValid fmt.toFormat (.finite s m e hm)) :
    fmt.toFloatFormat.IsValidFloat (m * 2 ^ e : NNReal) := by
  rcases h with _ | _ | _ | ⟨-, hmant, he⟩
  refine .intro_lt ?_ ?_ ?_
  · rw [hmant]
    simp [Format.targetExponent]
  · simpa using he
  · simp [← Nat.log2_lt hm.ne']
    grind [Format.targetExponent, totalExponent, CommonFormat.mantissaBits_toFormat]

lemma ofUnpackedFloat_finite_of_isValid {s m e hm}
    (h : IsValid fmt.toFormat (.finite s m e hm)) :
    ofUnpackedFloat (.finite s m e hm) =
      .ofValidNNReal (ofSign s) (m * 2 ^ e) (isValidFloat_of_isValid_finite h) := by
  rw [ofUnpackedFloat, RealFloat.roundNNReal_eq_ofValidNNReal (isValidFloat_of_isValid_finite h)]

lemma toUnpackedFloat_ofUnpackedFloat {x : UnpackedFloat} (h : IsValid fmt.toFormat x) :
    toUnpackedFloat (ofUnpackedFloat x : RealFloat fmt.toFloatFormat) = x := by
  fun_cases ofUnpackedFloat <;> (try simp [toUnpackedFloat]; done)
  rename_i s m e hm
  rw [RealFloat.roundNNReal_eq_ofValidNNReal (isValidFloat_of_isValid_finite h)]
  rcases h with _ | _ | _ | ⟨-, hmant, he⟩
  suffices fmt.toFloatFormat.getExponent (m * 2 ^ e) = e by
    simp [toUnpackedFloat, hm.ne', zpow_ne_zero, this, FloatFormat.getMantissa]
  simp [FloatFormat.getExponent, hm.ne', zpow_ne_zero, hm, ← Nat.log2_eq_log_two]
  grind [Format.targetExponent, totalExponent, Format.mantissaBits, Format.minExponent]

@[simp]
lemma IsValid.neg {fmt : Format} {x : UnpackedFloat} (h : IsValid fmt x) :
    IsValid fmt x.neg := by
  cases x <;> cases h <;> simp [UnpackedFloat.neg] <;> constructor <;> assumption

@[simp]
lemma isValid_unpack {spec : Format} {x : BitVec spec.numBits}
    (hspec : 2 ≤ spec.exponentBits := by decide) :
    IsValid spec (UnpackedFloat.unpack spec x) := by
  have : 2 ^ spec.exponentBits = 2 ^ (spec.exponentBits - 1) * 2 := by
    rw [← Nat.pow_add_one, Nat.sub_one_add_one spec.he.ne']
  have : 2 ≤ 2 ^ (spec.exponentBits - 1) := by
    simpa using Nat.pow_le_pow_right two_pos (Nat.sub_le_sub_right hspec 1)
  fun_cases UnpackedFloat.unpack
  · constructor
  · constructor
  · constructor
  · -- subnormal
    rename_i mvec evec exp svec s h₁ h₂ h₃
    have := mvec.log2_toNat_lt spec.hm.ne'
    constructor <;> simp [exp, h₂, totalExponent, Format.targetExponent, Format.mantissaBits,
      Format.minExponent, Format.exponentBias, Float.Model.Format.infinityExponent] <;> lia
  · -- normal
    rename_i mvec evec exp svec s h₁ h₂
    have : 0 < evec.toNat := by grind
    have : evec.toNat < 2 ^ spec.exponentBits - 1 := by
      simpa only [← BitVec.allOnes_le_iff, BitVec.neg_one_eq_allOnes, BitVec.not_le,
        BitVec.lt_def, BitVec.toNat_allOnes] using h₁
    simp only [BitVec.toNat_append_eq_add, BitVec.toNat_ofNat, pow_one, Nat.mod_succ, one_mul]
    constructor <;> format_trivial

lemma unpack_pack {spec : Format} {x : UnpackedFloat} (h : IsValid spec x)
    (hspec : 2 ≤ spec.exponentBits := by decide) :
    UnpackedFloat.unpack spec (UnpackedFloat.pack spec x) = x := by
  have : (2 : ℤ) ^ spec.exponentBits = 2 ^ (spec.exponentBits - 1) * 2 := by
    norm_cast
    rw [← Nat.pow_add_one, Nat.sub_one_add_one spec.he.ne']
  have : 2 ≤ (2 : ℤ) ^ (spec.exponentBits - 1) := by
    norm_cast
    simpa using Nat.pow_le_pow_right two_pos (Nat.sub_le_sub_right hspec 1)
  fun_cases UnpackedFloat.pack
  · simp
  · simp
  · simp
  · -- overflow! (impossible)
    rename_i s m e hm bexp hbexp
    rcases h with _ | _ | _ | ⟨-, hmant, hexp⟩
    format_trivial
  · -- normal
    rename_i s m e hm mbits bexp hbexp hmbits
    rcases h with _ | _ | _ | ⟨-, hmant, hexp⟩
    simp only [Format.mantissaBits, add_comm, Nat.add_right_cancel_iff] at hmbits
    have hbexp_pos : 0 < bexp := by format_trivial
    have hbexp_lt : bexp < 2 ^ spec.exponentBits := by lia
    have hbexp_lt' : bexp < 2 ^ spec.exponentBits - 1 := by lia
    have hdiv : m / 2 ^ spec.mantissaBitsWithoutImplicit = 1 := by
      rw [Nat.div_eq_iff (by positivity)]
      simp [← Nat.le_log2, hm.ne', Nat.le_sub_one_iff_lt,
        ← Nat.two_pow_succ, ← Nat.log2_lt, hmbits, mbits]
    replace hdiv := Nat.mul_one _ ▸ hdiv ▸ Nat.div_add_mod m (2 ^ spec.mantissaBitsWithoutImplicit)
    simp [UnpackedFloat.unpack, ← BitVec.toNat_inj, BitVec.neg_one_eq_allOnes,
      Nat.mod_eq_of_lt hbexp_lt, hbexp_lt'.ne, hbexp_pos.ne', -BitVec.toNat_append,
      BitVec.toNat_append_eq_add, hdiv]
    format_trivial
  · -- subnormal
    rename_i s m e hm mbits bexp hbexp hmbits
    rcases h with _ | _ | _ | ⟨-, hmant, hexp⟩
    replace hmbits : mbits < spec.mantissaBitsWithoutImplicit := by format_trivial
    have : m < 2 ^ spec.mantissaBitsWithoutImplicit := (Nat.log2_lt hm.ne').mp hmbits
    rw [UnpackedFloat.unpack]
    simp only [UnpackedFloat.unpackExponent_packComponents, BitVec.zero_eq_neg_one_iff, spec.he.ne',
      ↓reduceIte, UnpackedFloat.unpackMantissa_packComponents,
      UnpackedFloat.unpackSign_packComponents, UnpackedFloat.Sign.ofBitVec_toBitVec,
      BitVec.toNat_ofNat, Nat.zero_mod, Nat.cast_zero, zero_sub, neg_add_rev]
    simp [← BitVec.toNat_inj, Nat.mod_eq_of_lt this, hm.ne']
    format_trivial

end LeanFloats.UnpackedFloat
