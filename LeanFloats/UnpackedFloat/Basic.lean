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

variable {fmt : CommonFormat}

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

noncomputable def toUnpackedFloat (x : RealFloat fmt.toFloatFormat) : UnpackedFloat :=
  match x with
  | .ofValidNNReal s x h =>
    if hx : x = 0 then
      .zero (mkSign s)
    else
      .finite (mkSign s) (fmt.toFloatFormat.getMantissa x).natAbs (fmt.toFloatFormat.getExponent x) ?_
  | .infinity s => .infinity (mkSign s)
  | .nan => .notANumber
where finally simp [h.isRounded.getMantissa_eq_zero_iff, hx]

noncomputable def ofUnpackedFloat (x : UnpackedFloat) : RealFloat fmt.toFloatFormat :=
  match x with
  | .notANumber => .nan
  | .infinity s => .infinity (ofSign s)
  | .zero s => .ofValidNNReal (ofSign s) 0 (id fmt.toFloatFormat.isValidFloat_zero)
  | .finite s m e _hm => .roundNNReal (ofSign s) (m * 2 ^ e)

@[simp]
lemma toUnpackedFloat_nan :
    toUnpackedFloat (.nan : RealFloat fmt.toFloatFormat) = .notANumber := (rfl)

@[simp]
lemma toUnpackedFloat_infinity :
    toUnpackedFloat (.infinity s : RealFloat fmt.toFloatFormat) = .infinity (mkSign s) := (rfl)

@[simp]
lemma toUnpackedFloat_zero :
    toUnpackedFloat (.ofValidNNReal s 0 (by simp) : RealFloat fmt.toFloatFormat) =
      .zero (mkSign s) := by
  simp [toUnpackedFloat]

@[simp]
lemma ofUnpackedFloat_notANumber :
    (ofUnpackedFloat .notANumber : RealFloat fmt.toFloatFormat) = .nan := (rfl)

@[simp]
lemma ofUnpackedFloat_infinity :
    (ofUnpackedFloat (.infinity s) : RealFloat fmt.toFloatFormat) = .infinity (ofSign s) := (rfl)

@[simp]
lemma ofUnpackedFloat_zero :
    (ofUnpackedFloat (.zero s) : RealFloat fmt.toFloatFormat) =
      .ofValidNNReal (ofSign s) 0 (id fmt.toFloatFormat.isValidFloat_zero) := (rfl)

lemma ofUnpackedFloat_finite {s m e h} :
    (ofUnpackedFloat (.finite s m e h) : RealFloat fmt.toFloatFormat) =
      .roundNNReal (ofSign s) (m * 2 ^ e) := (rfl)

@[simp]
lemma ofUnpackedFloat_toUnpackedFloat (x : RealFloat fmt.toFloatFormat) :
    ofUnpackedFloat (toUnpackedFloat x) = x := by
  fun_cases toUnpackedFloat
  · simp
  · rename_i s x h h'
    have := h.isRounded.abs_getMantissa_mul_base_pow_getExponent
    simp only [Base.value_ofNat, Nat.cast_ofNat, NNReal.abs_eq] at this
    simp [ofUnpackedFloat_finite, this, RealFloat.roundNNReal_eq_roundReal,
      RealFloat.roundReal_eq_ofValidNNReal h]
  · simp
  · simp

@[simp]
lemma toUnpackedFloat_inj {x y : RealFloat fmt.toFloatFormat} :
    toUnpackedFloat x = toUnpackedFloat y ↔ x = y :=
  (Function.LeftInverse.injective ofUnpackedFloat_toUnpackedFloat).eq_iff

@[simp]
lemma signApply_eq_ofSign_mul (s : UnpackedFloat.Sign) (z : ℤ) :
    s.apply z = ofSign s * z := by
  cases s <;> simp [UnpackedFloat.Sign.apply]

lemma getExponent_eq_targetExponent {mant : ℕ} {f : ℝ} {exp : ℤ}
    (hmant : mant ≠ 0) (hf₁ : 0 ≤ f) (hf₂ : f < 1) :
    fmt.toFloatFormat.getExponent ((mant + f) * 2 ^ exp) =
      fmt.toFormat.targetExponent (totalExponent mant exp) := by
  simp [totalExponent, Format.targetExponent, FloatFormat.getExponent,
    zpow_ne_zero, show 0 < mant + f by positivity, ne_of_gt, abs_of_pos,
    Int.log_natCast_add_eq_natLog hmant.pos hf₁ hf₂, ← Nat.log2_eq_log_two,
    Format.mantissaBits, Format.minExponent, FloatFormat.minExp, ← sub_sub,
    add_right_comm, sub_right_comm _ _ (1 : ℤ)]

end LeanFloats.UnpackedFloat
