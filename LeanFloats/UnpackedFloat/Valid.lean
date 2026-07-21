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

inductive IsRounded (fmt : Format) : UnpackedFloat → Prop where
  | notANumber : IsRounded fmt .notANumber
  | infinity {s} : IsRounded fmt (.infinity s)
  | zero {s} : IsRounded fmt (.zero s)
  | finite {s m e} (hm) (hmant : e = fmt.targetExponent (totalExponent m e)) :
    IsRounded fmt (.finite s m e hm)

inductive IsValid (fmt : Format) : UnpackedFloat → Prop where
  | notANumber : IsValid fmt .notANumber
  | infinity {s} : IsValid fmt (.infinity s)
  | zero {s} : IsValid fmt (.zero s)
  | finite {s m e} (hm) (hmant : e = fmt.targetExponent (totalExponent m e))
    (he : e ≤ fmt.infinityExponent - fmt.mantissaBits) :
    IsValid fmt (.finite s m e hm)

attribute [simp] IsValid.notANumber IsRounded.notANumber IsValid.infinity IsRounded.infinity
  IsValid.zero IsRounded.zero

lemma isRounded_iff (fmt : Format) (x : UnpackedFloat) :
    IsRounded fmt x ↔ ∀ s m e hm, x = .finite s m e hm → e = fmt.targetExponent (totalExponent m e) := by
  grind [IsRounded, UnpackedFloat]

lemma isValid_iff (fmt : Format) (x : UnpackedFloat) :
    IsValid fmt x ↔ ∀ s m e hm, x = .finite s m e hm →
      e = fmt.targetExponent (totalExponent m e) ∧ e ≤ fmt.infinityExponent - fmt.mantissaBits := by
  grind [IsValid, UnpackedFloat]

lemma IsValid.isRounded {fmt : Format} {x : UnpackedFloat}
    (h : IsValid fmt x) : IsRounded fmt x := by
  grind [IsValid, IsRounded]

def bound (fmt : Format) (x : UnpackedFloat) : UnpackedFloat :=
  match x with
  | .finite s _ e _ =>
    if e ≤ fmt.infinityExponent - fmt.mantissaBits then
      x
    else
      .infinity s
  | _ => x

@[simp]
lemma isValid_bound {fmt : Format} {x : UnpackedFloat}
    (h : IsRounded fmt x) : IsValid fmt (bound fmt x) := by
  grind [IsValid, IsRounded, bound]

@[simp]
lemma bound_eq_self {fmt : Format} {x : UnpackedFloat}
    (h : IsValid fmt x) : bound fmt x = x := by
  grind [IsValid, bound]

variable {fmt : CommonFormat}

@[simp]
lemma isRounded_ofUnboundedFloat {fmt fmt' common}
    [HasCommonOfFormat fmt common]
    [HasCommonOfFloatFormat fmt' common]
    (x : UnboundedFloat fmt') : IsRounded fmt (ofUnboundedFloat x) := by
  cases HasCommonOfFormat.elim fmt
  cases HasCommonOfFloatFormat.elim fmt'
  fun_cases ofUnboundedFloat
  · constructor
  · rename_i s x h hx
    constructor
    rw [← getExponent_eq_targetExponent (f := 0) _ (by simp) (by simp)]
    · congr 1; symm
      simpa using h.abs_getMantissa_mul_base_pow_getExponent
    · simp [h.getMantissa_eq_zero_iff, hx]
  · constructor
  · constructor

lemma isRounded_of_isRounded_finite {s m e hm}
    (h : IsRounded fmt.toFormat (.finite s m e hm)) :
    fmt.toFloatFormat.IsRounded (m * 2 ^ e : NNReal) := by
  rcases h with _ | _ | _ | ⟨-, hmant⟩
  refine .intro_le ?_ ?_
  · rw [hmant]
    simp [Format.targetExponent]
  · apply le_of_lt
    simp [← Nat.log2_lt hm.ne']
    format_trivial

lemma isValidFloat_of_isValid_finite {s m e hm}
    (h : IsValid fmt.toFormat (.finite s m e hm)) :
    fmt.toFloatFormat.IsValidFloat (m * 2 ^ e : NNReal) := by
  rcases h with _ | _ | _ | ⟨-, hmant, he⟩
  refine .intro_lt ?_ ?_ ?_
  · rw [hmant]
    simp [Format.targetExponent]
  · simpa using he
  · simp [← Nat.log2_lt hm.ne']
    format_trivial

lemma toUnboundedFloat_finite_of_isRounded {s m e hm}
    (h : IsRounded fmt.toFormat (.finite s m e hm)) :
    toUnboundedFloat (.finite s m e hm) =
      .ofValidNNReal (ofSign s) (m * 2 ^ e) (isRounded_of_isRounded_finite h) := by
  rw [toUnboundedFloat, UnboundedFloat.roundNNReal_eq_ofValidNNReal (isRounded_of_isRounded_finite h)]

lemma getExponent_of_isRounded_finite {s m e hm}
    (h : IsRounded fmt.toFormat (.finite s m e hm)) :
    fmt.toFloatFormat.getExponent (m * 2 ^ e) = e := by
  rw [← add_zero (m : ℝ), getExponent_eq_targetExponent (by simp [hm.ne']) le_rfl one_pos]
  rcases h with _ | _ | _ | ⟨-, hmant⟩
  rw [← hmant]

lemma getMantissa_of_isRounded_finite {s m e hm}
    (h : IsRounded fmt.toFormat (.finite s m e hm)) :
    fmt.toFloatFormat.getMantissa (m * 2 ^ e) = m := by
  simpa using fmt.toFloatFormat.getMantissa_mul_base_pow (getExponent_of_isRounded_finite h)

@[simp]
lemma ofUnboundedFloat_toUnboundedFloat {fmt common} [HasCommonOfFloatFormat fmt common]
    {x : UnpackedFloat} (h : IsRounded common.toFormat x) :
    ofUnboundedFloat (toUnboundedFloat x : UnboundedFloat fmt) = x := by
  cases HasCommonOfFloatFormat.elim fmt
  fun_cases toUnboundedFloat <;> (try simp [ofUnboundedFloat]; done)
  rename_i s m e hm
  rw [UnboundedFloat.roundNNReal_eq_ofValidNNReal (isRounded_of_isRounded_finite h)]
  rcases h with _ | _ | _ | ⟨-, hmant⟩
  suffices common.toFloatFormat.getExponent (m * 2 ^ e) = e by
    simp [ofUnboundedFloat, hm.ne', zpow_ne_zero, this, FloatFormat.getMantissa]
  simp [FloatFormat.getExponent, hm.ne', zpow_ne_zero, hm, ← Nat.log2_eq_log_two]
  format_trivial

lemma isValid_iff_isRounded_and_inRange {x : UnpackedFloat} :
    IsValid fmt.toFormat x ↔ IsRounded fmt.toFormat x ∧
      fmt.toFloatFormat.InRange (toUnboundedFloat x : UnboundedFloat fmt.toFloatFormat).toFiniteReal := by
  fun_cases toUnboundedFloat
  · simp
  · simp
  · simp
  · rename_i s m e hm
    constructor
    · intro h
      constructor
      · exact h.isRounded
      · rw [UnboundedFloat.roundNNReal_eq_ofValidNNReal (isRounded_of_isRounded_finite h.isRounded)]
        simpa using (isValidFloat_of_isValid_finite h).inRange
    · intro ⟨h₁, h₂⟩
      rw [UnboundedFloat.roundNNReal_eq_ofValidNNReal (isRounded_of_isRounded_finite h₁)] at h₂
      simp only [UnboundedFloat.toFiniteReal_ofValidNNReal, NNReal.coe_mul, NNReal.coe_natCast,
        NNReal.coe_zpow, NNReal.coe_ofNat, FloatFormat.inRange_simpleSign_mul_iff] at h₂
      rcases h₁ with _ | _ | _ | ⟨-, hmant⟩
      constructor
      · assumption
      · have := h₂.getExponent_le
        rw [← add_zero (m : ℝ), getExponent_eq_targetExponent (by simp [hm.ne']) (by simp) (by simp)] at this
        simpa [← hmant] using this

@[simp]
lemma inRange_toUnboundedFloat {fmt common} [HasCommonOfFloatFormat fmt common]
    {x : UnpackedFloat} (h : IsValid common.toFormat x) :
    fmt.InRange (toUnboundedFloat x : UnboundedFloat fmt).toFiniteReal := by
  cases HasCommonOfFloatFormat.elim fmt
  exact (isValid_iff_isRounded_and_inRange.mp h).2

@[simp]
lemma isValid_ofUnboundedFloat_toUnbounded {fmt fmt' common} [HasCommonOfFormat fmt common]
    [HasCommonOfFloatFormat fmt' common] (x : RealFloat fmt') : IsValid fmt (ofUnboundedFloat x.toUnbounded) := by
  cases HasCommonOfFormat.elim fmt
  cases HasCommonOfFloatFormat.elim fmt'
  simp [isValid_iff_isRounded_and_inRange]

@[simp]
lemma ofUnbounded_toUnboundedFloat_bound {fmt fmt' common}
    [HasCommonOfFormat fmt common] [HasCommonOfFloatFormat fmt' common]
    {x : UnpackedFloat} (h : IsRounded fmt x) :
    RealFloat.ofUnbounded (toUnboundedFloat (bound fmt x) : UnboundedFloat fmt') =
      RealFloat.ofUnbounded (toUnboundedFloat x) := by
  cases HasCommonOfFormat.elim fmt
  cases HasCommonOfFloatFormat.elim fmt'
  cases x
  · simp
  · simp
  · simp
  · rename_i s m e hm
    rw [bound]
    split
    · rfl
    · have : ¬ IsValid common.toFormat (.finite s m e hm) := by
        rintro (_ | _ | _ | ⟨-, hmant, hexp⟩)
        contradiction
      simp only [isValid_iff_isRounded_and_inRange, h, true_and] at this
      simp_all [toUnboundedFloat_finite, RealFloat.ofUnbounded, RealFloat.overflowValue]

@[simp]
lemma IsRounded.neg {fmt : Format} {x : UnpackedFloat} (h : IsRounded fmt x) :
    IsRounded fmt x.neg := by
  cases x <;> cases h <;> simp [UnpackedFloat.neg]; constructor; assumption

@[simp]
lemma IsValid.neg {fmt : Format} {x : UnpackedFloat} (h : IsValid fmt x) :
    IsValid fmt x.neg := by
  cases x <;> cases h <;> simp [UnpackedFloat.neg]; constructor <;> assumption

@[simp]
lemma IsRounded.abs {fmt : Format} {x : UnpackedFloat} (h : IsRounded fmt x) :
    IsRounded fmt x.abs := by
  cases x <;> cases h <;> simp [UnpackedFloat.abs]; constructor; assumption

@[simp]
lemma IsValid.abs {fmt : Format} {x : UnpackedFloat} (h : IsValid fmt x) :
    IsValid fmt x.abs := by
  cases x <;> cases h <;> simp [UnpackedFloat.abs]; constructor <;> assumption

@[simp]
lemma isValid_unpack {spec : Format} {x : BitVec spec.numBits} [GoodFormat spec] :
    IsValid spec (UnpackedFloat.unpack spec x) := by
  have : 2 ^ spec.exponentBits = 2 ^ (spec.exponentBits - 1) * 2 := by
    rw [← Nat.pow_add_one, Nat.sub_one_add_one spec.he.ne']
  have : 2 ≤ 2 ^ (spec.exponentBits - 1) := by
    simpa using Nat.pow_le_pow_right two_pos (Nat.sub_le_sub_right GoodFormat.exponentBits_ge 1)
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

@[simp]
lemma isRounded_unpack {spec : Format} {x : BitVec spec.numBits} [GoodFormat spec] :
    IsRounded spec (UnpackedFloat.unpack spec x) :=
  isValid_unpack.isRounded

@[simp]
lemma unpack_pack {spec : Format} {x : UnpackedFloat} (h : IsRounded spec x) [GoodFormat spec] :
    UnpackedFloat.unpack spec (UnpackedFloat.pack spec x) = bound spec x := by
  have : (2 : ℤ) ^ spec.exponentBits = 2 ^ (spec.exponentBits - 1) * 2 := by
    norm_cast
    rw [← Nat.pow_add_one, Nat.sub_one_add_one spec.he.ne']
  have : 2 ≤ (2 : ℤ) ^ (spec.exponentBits - 1) := by
    norm_cast
    simpa using Nat.pow_le_pow_right two_pos (Nat.sub_le_sub_right GoodFormat.exponentBits_ge 1)
  fun_cases UnpackedFloat.pack
  · simp
  · simp
  · simp
  · -- overflow!
    rename_i s m e hm bexp hbexp
    rcases h with _ | _ | _ | ⟨-, hmant⟩
    simp [bound]
    format_trivial
  · -- normal
    rename_i s m e hm mbits bexp hbexp hmbits
    rcases h with _ | _ | _ | ⟨-, hmant⟩
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
      BitVec.toNat_append_eq_add, hdiv, bound]
    format_trivial
  · -- subnormal
    rename_i s m e hm mbits bexp hbexp hmbits
    rcases h with _ | _ | _ | ⟨-, hmant⟩
    replace hmbits : mbits < spec.mantissaBitsWithoutImplicit := by format_trivial
    have : m < 2 ^ spec.mantissaBitsWithoutImplicit := (Nat.log2_lt hm.ne').mp hmbits
    rw [UnpackedFloat.unpack]
    simp only [UnpackedFloat.unpackExponent_packComponents, BitVec.zero_eq_neg_one_iff, spec.he.ne',
      ↓reduceIte, UnpackedFloat.unpackMantissa_packComponents,
      UnpackedFloat.unpackSign_packComponents, UnpackedFloat.Sign.ofBitVec_toBitVec,
      BitVec.toNat_ofNat, Nat.zero_mod, Nat.cast_zero, zero_sub, neg_add_rev]
    simp [← BitVec.toNat_inj, Nat.mod_eq_of_lt this, hm.ne', bound]
    format_trivial

end LeanFloats.UnpackedFloat
