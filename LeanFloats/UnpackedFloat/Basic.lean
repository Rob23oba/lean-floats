module
public import LeanFloats.RealFloats.Rounding
public import LeanFloats.UnpackedFloat.FormatTrivial

@[expose] public section

namespace LeanFloats.UnpackedFloat

open Float.Model

structure CommonFormat where
  ebits : Nat
  mbits : Nat
  mbits_pos : 0 < mbits := by decide
  mbits_lt : mbits + 1 < 2 ^ (ebits - 1) := by decide

abbrev CommonFormat.binary32 : CommonFormat where
  ebits := 8
  mbits := 23

abbrev CommonFormat.binary64 : CommonFormat where
  ebits := 11
  mbits := 52

abbrev CommonFormat.toFloatFormat (c : CommonFormat) : FloatFormat 2 where
  infExp := 2 ^ (c.ebits - 1)
  precision := c.mbits + 1
  precision_pos := by simp
  precision_lt_infExp := c.mbits_lt

abbrev CommonFormat.toFormat (c : CommonFormat) : Format where
  mantissaBitsWithoutImplicit := c.mbits
  exponentBits := c.ebits
  hm := c.mbits_pos
  he := by grind [c.mbits_lt]

class GoodFormat (f : Format) where
  exponentBits_ge : 2 ≤ f.exponentBits := by decide

class HasCommonOfFormat (f : Format) (c : outParam CommonFormat) where
  elim (f) : f = c.toFormat := by rfl

class HasCommonOfFloatFormat (f : FloatFormat 2) (c : outParam CommonFormat) where
  elim (f) : f = c.toFloatFormat := by rfl

instance (c : CommonFormat) : HasCommonOfFormat c.toFormat c where
instance (c : CommonFormat) : HasCommonOfFloatFormat c.toFloatFormat c where

instance : GoodFormat .binary32 where
instance : GoodFormat .binary64 where
instance : HasCommonOfFormat .binary32 .binary32 where
instance : HasCommonOfFormat .binary64 .binary64 where
instance : HasCommonOfFloatFormat .binary32 .binary32 where
instance : HasCommonOfFloatFormat .binary64 .binary64 where

@[simp]
lemma CommonFormat.mantissaBits_toFormat (c : CommonFormat) : c.toFormat.mantissaBits = c.toFloatFormat.precision := by
  simp [Format.mantissaBits, add_comm]

@[simp]
lemma CommonFormat.minExponent_toFormat (c : CommonFormat) : c.toFormat.minExponent = c.toFloatFormat.minExp := by
  simp [Format.minExponent, FloatFormat.minExp, Format.mantissaBits, add_comm]

@[simp]
lemma CommonFormat.two_le_toFormat_exponentBits (c : CommonFormat) :
    2 ≤ c.toFormat.exponentBits := by
  have := c.mbits_lt
  simp only [ge_iff_le]
  grind

instance (c : CommonFormat) : GoodFormat c.toFormat where
  exponentBits_ge := c.two_le_toFormat_exponentBits

def mkSign (s : SimpleSign) : UnpackedFloat.Sign :=
  match s with
  | 1 => .positive
  | -1 => .negative

def ofSign (s : UnpackedFloat.Sign) : SimpleSign :=
  match s with
  | .positive => 1
  | .negative => -1

@[simp] lemma ofSign_negative : ofSign .negative = -1 := rfl
@[simp] lemma ofSign_positive : ofSign .positive = 1 := rfl

@[simp] lemma mkSign_neg_one : mkSign (-1) = .negative := rfl
@[simp] lemma mkSign_one : mkSign 1 = .positive := rfl

@[simp] lemma ofSign_mkSign (s) : ofSign (mkSign s) = s := by cases s <;> rfl
@[simp] lemma mkSign_ofSign (s) : mkSign (ofSign s) = s := by cases s <;> rfl

@[simp] lemma ofSign_inj {a b} : ofSign a = ofSign b ↔ a = b := by cases a <;> cases b <;> simp
@[simp] lemma mkSign_inj {a b} : mkSign a = mkSign b ↔ a = b := by cases a <;> cases b <;> simp

@[simp] lemma ofSign_neg {a} : ofSign (-a) = -ofSign a := by cases a <;> rfl
@[simp] lemma ofSign_mul {a b} : ofSign (a * b) = ofSign a * ofSign b := by cases a <;> cases b <;> rfl
@[simp] lemma ofSign_div {a b} : ofSign (a / b) = ofSign a * ofSign b := by cases a <;> cases b <;> rfl

noncomputable def ofUnboundedFloat {fmt : FloatFormat 2} (x : UnboundedFloat fmt) : UnpackedFloat :=
  match x with
  | .ofValidNNReal s x h =>
    if hx : x = 0 then
      .zero (mkSign s)
    else
      .finite (mkSign s) (fmt.getMantissa x).natAbs (fmt.getExponent x) ?_
  | .infinity s => .infinity (mkSign s)
  | .nan => .notANumber
where finally simp [h.getMantissa_eq_zero_iff, hx]

noncomputable def toUnboundedFloat {fmt : FloatFormat 2} (x : UnpackedFloat) : UnboundedFloat fmt :=
  match x with
  | .notANumber => .nan
  | .infinity s => .infinity (ofSign s)
  | .zero s => .ofValidNNReal (ofSign s) 0 (by simp)
  | .finite s m e _hm => .roundNNReal (ofSign s) (m * 2 ^ e)

variable {fmt : FloatFormat 2}

@[simp]
lemma ofUnboundedFloat_nan :
    ofUnboundedFloat (.nan : UnboundedFloat fmt) = .notANumber := (rfl)

@[simp]
lemma ofUnboundedFloat_infinity {s} :
    ofUnboundedFloat (.infinity s : UnboundedFloat fmt) = .infinity (mkSign s) := (rfl)

@[simp]
lemma ofUnboundedFloat_zero {s} :
    ofUnboundedFloat (.ofValidNNReal s 0 (by simp) : UnboundedFloat fmt) =
      .zero (mkSign s) := by
  simp [ofUnboundedFloat]

@[simp]
lemma toUnboundedFloat_notANumber :
    (toUnboundedFloat .notANumber : UnboundedFloat fmt) = .nan := (rfl)

@[simp]
lemma toUnboundedFloat_infinity {s} :
    (toUnboundedFloat (.infinity s) : UnboundedFloat fmt) = .infinity (ofSign s) := (rfl)

@[simp]
lemma toUnboundedFloat_zero {s} :
    (toUnboundedFloat (.zero s) : UnboundedFloat fmt) =
      .ofValidNNReal (ofSign s) 0 (by simp) := (rfl)

lemma toUnboundedFloat_finite {s m e h} :
    (toUnboundedFloat (.finite s m e h) : UnboundedFloat fmt) =
      .roundNNReal (ofSign s) (m * 2 ^ e) := (rfl)

@[simp]
lemma toUnboundedFloat_ofUnboundedFloat (x : UnboundedFloat fmt) :
    toUnboundedFloat (ofUnboundedFloat x) = x := by
  fun_cases ofUnboundedFloat
  · simp
  · rename_i s x h h'
    have := h.abs_getMantissa_mul_base_pow_getExponent
    simp only [Base.value_ofNat, Nat.cast_ofNat, NNReal.abs_eq] at this
    simp [toUnboundedFloat_finite, this, UnboundedFloat.roundNNReal_eq_roundReal,
      UnboundedFloat.roundReal_eq_ofValidNNReal h]
  · simp
  · simp

@[simp]
lemma ofUnboundedFloat_inj {x y : UnboundedFloat fmt} :
    ofUnboundedFloat x = ofUnboundedFloat y ↔ x = y :=
  (Function.LeftInverse.injective toUnboundedFloat_ofUnboundedFloat).eq_iff

@[simp]
lemma signApply_eq_ofSign_mul (s : UnpackedFloat.Sign) (z : ℤ) :
    s.apply z = ofSign s * z := by
  cases s <;> simp [UnpackedFloat.Sign.apply]

lemma getExponent_eq_targetExponent {fmt : CommonFormat} {mant : ℕ} {f : ℝ} {exp : ℤ}
    (hmant : mant = 0 → exp ≤ fmt.toFormat.minExponent) (hf₁ : 0 ≤ f) (hf₂ : f < 1) :
    fmt.toFloatFormat.getExponent ((mant + f) * 2 ^ exp) =
      fmt.toFormat.targetExponent (totalExponent mant exp) := by
  by_cases! hmant' : mant ≠ 0
  · simp [totalExponent, Format.targetExponent, FloatFormat.getExponent,
      show 0 < mant + f by positivity, ne_of_gt, abs_of_pos,
      Int.log_natCast_add_eq_natLog hmant'.pos hf₁ hf₂, ← Nat.log2_eq_log_two,
      Format.mantissaBits, Format.minExponent, FloatFormat.minExp, ← sub_sub,
      add_right_comm, sub_right_comm _ _ (1 : ℤ)]
  · subst hmant'
    simp only [CommonFormat.minExponent_toFormat, forall_const] at hmant
    have htarget : fmt.toFormat.targetExponent (totalExponent 0 exp) = fmt.toFormat.minExponent := by
      format_trivial
    suffices |f| < 2 ^ (fmt.toFloatFormat.minExp + (↑fmt.mbits + 1) - exp) by
      simpa [FloatFormat.getExponent_eq_minExp_iff, htarget, ← lt_div_iff₀, ← zpow_sub₀]
    grw [abs_of_nonneg hf₁, hf₂]
    apply one_le_zpow₀ one_le_two
    format_trivial

end LeanFloats.UnpackedFloat
