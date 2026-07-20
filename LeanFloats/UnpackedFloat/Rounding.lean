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

inductive AccuracyRepresents : UnpackedFloat.Accuracy → ℝ → Prop where
  | exact {x} (h : x = 0) : AccuracyRepresents .exact x
  | inexact {x ord} (hgt : 0 < x) (hlt : x < 1) (hcmp : compare x (2⁻¹) = ord) :
    AccuracyRepresents (.inexact ord) x

lemma AccuracyRepresents.lt_one {acc : UnpackedFloat.Accuracy} {f : ℝ}
    (h : AccuracyRepresents acc f) : f < 1 := by grind [AccuracyRepresents]

lemma AccuracyRepresents.nonneg {acc : UnpackedFloat.Accuracy} {f : ℝ}
    (h : AccuracyRepresents acc f) : 0 ≤ f := by grind [AccuracyRepresents]

protected lemma AccuracyRepresents.roundToNearestEven
    {acc : UnpackedFloat.Accuracy} {f : ℝ} {n : ℕ} (h : AccuracyRepresents acc f) :
    acc.roundToNearestEven n = RoundingFunction.tiesToEven (n + f) := by
  rcases h with (rfl | @⟨_, _ | _ | _, hgt, hlt, hcmp⟩)
  · simp [UnpackedFloat.Accuracy.roundToNearestEven]
  · rw [compare_lt_iff_lt] at hcmp
    rw [RoundingFunction.apply_natCast_add_of_abs_lt (by grind),
      UnpackedFloat.Accuracy.roundToNearestEven]
  · rw [compare_eq_iff_eq] at hcmp
    rw [hcmp]
    by_cases hn : Even n
    · rw [RoundingFunction.tiesToEven_natCast_add_of_even hn (by simp)]
      simpa [UnpackedFloat.Accuracy.roundToNearestEven,
        ← Int.dvd_iff_emod_eq_zero, ← even_iff_two_dvd] using hn
    · rw [show (n + 2⁻¹ : ℝ) = (n + 1 : ℕ) - 2⁻¹ by grind]
      rw [RoundingFunction.tiesToEven_natCast_sub_of_even (by grind) (by simp)]
      simp [UnpackedFloat.Accuracy.roundToNearestEven, ← Int.odd_iff, ← Int.not_even_iff_odd, hn]
  · rw [compare_gt_iff_gt] at hcmp
    rw [show n + f = (n + 1 : ℕ) - (1 - f) by grind]
    rw [RoundingFunction.apply_natCast_sub_of_abs_lt (by grind),
      UnpackedFloat.Accuracy.roundToNearestEven]

@[mk_iff]
structure ExtendedMantissaRepresents (x : UnpackedFloat.ExtendedMantissa) (v : Real) where
  mantissa_eq : x.mantissa = ⌊v⌋
  roundBit_iff : x.roundBit ↔ 2⁻¹ ≤ Int.fract v
  stickyBit_iff : x.stickyBit ↔ Int.fract (2 * v) ≠ 0

lemma fract_two_mul_eq_zero_iff (v : ℝ) :
    Int.fract (2 * v) = 0 ↔ Int.fract v = 0 ∨ Int.fract v = 2⁻¹ := by
  rw [show 2 * v = v * (2 : Nat) by simp [mul_comm]]
  rw [← Int.fract_fract_mul, Nat.cast_ofNat, Int.fract_eq_zero_iff, Set.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    have : 0 ≤ (y : ℝ) ∧ (y : ℝ) < 2 := by grind [Int.fract_nonneg, Int.fract_lt_one]
    norm_cast at this
    replace this : y = 0 ∨ y = 1 := by lia
    rcases this with rfl | rfl
    · simp_all
    · simp_all [← div_eq_iff]
  · rintro (h | h)
    · use 0; simp_all
    · use 1; simp_all

lemma extendedMantissaRepresents_natCast {x : UnpackedFloat.ExtendedMantissa} {n : ℕ} :
    ExtendedMantissaRepresents x n ↔ x.mantissa = n ∧ x.roundBit = false ∧ x.stickyBit = false := by
  norm_num [extendedMantissaRepresents_iff, fract_two_mul_eq_zero_iff]

protected lemma ExtendedMantissaRepresents.shiftRightOne
    {x : UnpackedFloat.ExtendedMantissa} {v : Real} (h : ExtendedMantissaRepresents x v) :
    ExtendedMantissaRepresents x.shiftRightOne (v/2) := by
  obtain ⟨mant_eq, round_eq, sticky_eq⟩ := h
  rw [UnpackedFloat.ExtendedMantissa.shiftRightOne]
  constructor
  · simp [mant_eq]
  · simp only [Nat.mod_two_bne_zero, beq_iff_eq]
    rw [show x.mantissa % 2 = 1 ↔ 1 ≤ (x.mantissa : ℤ) - x.mantissa / 2 * 2 by lia]
    have h₁ (a : ℝ) : 1 ≤ a ↔ 1 ≤ ⌊a⌋ := by simp [Int.le_floor]
    have h₂ (z : ℤ) : (z * 2 : ℝ) = (z * 2 : ℤ) := by simp
    simp [inv_le_iff_one_le_mul₀, Int.fract, sub_mul, mant_eq, h₁, h₂, -Int.cast_mul]
  · simp [round_eq, sticky_eq, mul_div_cancel₀, fract_two_mul_eq_zero_iff]
    grind

protected lemma AccuracyRepresents.extendedMantissa {acc f}
    (h : AccuracyRepresents acc f) (n : ℕ) :
    ExtendedMantissaRepresents (.ofMantissaAndAccuracy n acc) (n + f) := by
  rcases h with (rfl | @⟨_, _ | _ | _, hgt, hlt, hcmp⟩) <;>
    simp only [UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy] <;>
    (try simp only [compare_lt_iff_lt, compare_eq_iff_eq, compare_gt_iff_gt] at hcmp)
  · constructor <;> simp [fract_two_mul_eq_zero_iff]
  · constructor <;> simp (disch := grind) [Int.fract_eq_self.mpr, mul_add, *] <;> grind
  · constructor <;> simp (disch := grind) [Int.fract_eq_self.mpr, fract_two_mul_eq_zero_iff, *]; grind
  · constructor <;> simp (disch := grind) [Int.fract_eq_self.mpr, fract_two_mul_eq_zero_iff, *] <;> grind

protected lemma ExtendedMantissaRepresents.accuracy {emant} {x : ℝ}
    (h : ExtendedMantissaRepresents emant x) :
    AccuracyRepresents emant.accuracy (Int.fract x) := by
  rcases h with ⟨mant_eq, round_eq, sticky_eq⟩
  rcases emant with ⟨mant, _ | _, _ | _⟩ <;>
    simp only [Bool.false_eq_true, false_iff, not_le, ne_eq, Decidable.not_not, true_iff,
      UnpackedFloat.ExtendedMantissa.accuracy, fract_two_mul_eq_zero_iff] at mant_eq round_eq sticky_eq ⊢
  · constructor; grind
  · constructor <;> (try simp [compare_lt_iff_lt]) <;> grind [Int.fract_nonneg]
  · constructor <;> (try simp) <;> grind [Int.fract_lt_one]
  · constructor <;> (try simp [compare_gt_iff_gt]) <;> grind [Int.fract_lt_one]

protected lemma ExtendedMantissaRepresents.shiftRight
    {x : UnpackedFloat.ExtendedMantissa} {v : Real}
    (h : ExtendedMantissaRepresents x v) (n : ℕ) :
    ExtendedMantissaRepresents (x >>> n) (v / 2 ^ n) := by
  change ExtendedMantissaRepresents (n.repeat (·.shiftRightOne) x) (v / 2 ^ n)
  induction n with
  | zero => simp [Nat.repeat, h]
  | succ k ih => simpa [Nat.repeat, div_div, ← pow_succ] using ih.shiftRightOne

lemma decreaseExponent_eq {mant exp target} {mant' exp'}
    (h : UnpackedFloat.decreaseExponent mant exp target = (mant', exp')) :
    (mant * 2 ^ exp : NNReal) = mant' * 2 ^ exp' := by
  unfold UnpackedFloat.decreaseExponent at h
  cases h
  simp [Nat.shiftLeft_eq, ← zpow_natCast, mul_assoc, ← zpow_add₀]

lemma decreaseExponent_eq_min {mant exp target} {mant' exp'}
    (h : UnpackedFloat.decreaseExponent mant exp target = (mant', exp')) :
    exp' = min exp target := by
  unfold UnpackedFloat.decreaseExponent at h
  cases h
  lia

lemma shiftToExponent_spec {mant exp target acc emant exp' f}
    (hf : AccuracyRepresents acc f) (h : UnpackedFloat.shiftToExponent mant exp acc target = (emant, exp')) :
    ExtendedMantissaRepresents emant ((mant + f) * 2 ^ (exp - exp')) := by
  unfold UnpackedFloat.shiftToExponent at h
  extract_lets shift initemant at h
  cases h; subst initemant
  simpa [div_eq_mul_inv] using (hf.extendedMantissa mant).shiftRight shift

lemma shiftToExponent_eq_max {mant exp target acc emant exp'}
    (h : UnpackedFloat.shiftToExponent mant exp acc target = (emant, exp')) :
    exp' = max exp target := by
  unfold UnpackedFloat.shiftToExponent at h
  cases h
  lia

lemma getExponent_eq_targetExponent {mant : ℕ} {f : ℝ} {exp : ℤ}
    (hmant : mant ≠ 0) (hf₁ : 0 ≤ f) (hf₂ : f < 1) :
    fmt.toFloatFormat.getExponent ((mant + f) * 2 ^ exp) =
      fmt.toFormat.targetExponent (totalExponent mant exp) := by
  simp [totalExponent, Format.targetExponent, FloatFormat.getExponent,
    zpow_ne_zero, show 0 < mant + f by positivity, ne_of_gt, abs_of_pos,
    Int.log_natCast_add_eq_natLog hmant.pos hf₁ hf₂, ← Nat.log2_eq_log_two,
    Format.mantissaBits, Format.minExponent, FloatFormat.minExp, ← sub_sub,
    add_right_comm, sub_right_comm _ _ (1 : ℤ)]

-- TODO: cleanup / simplify / split
lemma ofUnpackedFloat_roundWithAccuracy {s : UnpackedFloat.Sign} {mant : ℕ} {exp : ℤ}
    {acc : UnpackedFloat.Accuracy} {f : NNReal} (hmant : mant ≠ 0)
    (hexp : exp ≤ fmt.toFormat.targetExponent (totalExponent mant exp))
    (hf : AccuracyRepresents acc f) :
    ofUnpackedFloat (UnpackedFloat.roundWithAccuracy fmt.toFormat s mant exp acc) =
      (.roundNNReal (ofSign s) ((mant + f) * 2 ^ exp) : RealFloat fmt.toFloatFormat) := by
  unfold UnpackedFloat.roundWithAccuracy
  split
  rename_i emant exp' h₁
  have hemant := shiftToExponent_spec hf h₁
  have hexp' := shiftToExponent_eq_max h₁
  rw [max_eq_right hexp] at hexp'
  extract_lets rounded
  have hrounded : rounded = RoundingFunction.tiesToEven ((mant + f) * 2 ^ (exp - exp')) := by
    unfold rounded
    rw [UnpackedFloat.ExtendedMantissa.roundedMantissa, hemant.accuracy.roundToNearestEven,
      ← Int.cast_natCast, hemant.mantissa_eq, Int.floor_add_fract]
  split
  rename_i femant fexp h₂
  extract_lets fmant
  have hfmant := show (fmant : ℤ) = _ from (shiftToExponent_spec (.exact rfl) h₂).mantissa_eq
  have hfexp := shiftToExponent_eq_max h₂
  rw [add_zero] at hfmant
  have hrounded_le : rounded ≤ 2 ^ (fmt.mbits + 1) := by
    zify
    rw [hrounded]
    apply RoundingFunction.apply_le_of_le_natCast
    apply le_of_lt
    simp only [hexp', Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast, Nat.ofNat_pos, zpow_pos,
      ← lt_div_iff₀, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ← zpow_sub₀]
    grw [hf.lt_one]
    norm_cast
    grw [Nat.add_one_le_of_lt Nat.lt_log2_self, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast]
    apply zpow_le_zpow_right₀ one_le_two
    format_trivial
  replace hfmant : fmant * (2 : ℝ) ^ fexp = rounded * 2 ^ exp' := by
    by_cases heqz : rounded = 0
    · clear *-hfmant heqz; simp_all
    rcases hrounded_le.lt_or_eq with hlt | heq
    · rw [← Nat.log2_lt heqz] at hlt
      have : fexp = exp' := by format_trivial
      subst this; clear *-hfmant; simp_all
    · rw [← Int.cast_natCast, hfmant]
      have : fexp = exp' + 1 := by clear *-hfexp hexp' heq; format_trivial
      clear *-this heq hfmant
      rw [← hfmant]
      replace hfmant : fmant = ⌊(2 ^ (fmt.mbits : ℤ) : ℝ)⌋ := by
        simpa [this, heq, ← zpow_natCast, ← zpow_sub_one₀] using hfmant
      norm_cast at hfmant
      rw [Int.floor_natCast] at hfmant
      norm_cast at hfmant
      simp_all [← zpow_natCast, ← zpow_add₀, ← add_assoc, add_right_comm]
  rw [RealFloat.roundNNReal]
  unfold RealFloat.roundReal
  extract_lets myexp myround
  have hmyexp : myexp = value_of% myexp := rfl
  have hmyround : myround = value_of% myround := rfl
  replace hmyexp : myexp = exp' := by
    simpa [getExponent_eq_targetExponent hmant hf.nonneg hf.lt_one, hexp'] using hmyexp
  replace hmyround : myround = ofSign s * (rounded * 2 ^ exp') := by
    rw [← Int.cast_natCast]
    simpa [hmyexp, mul_div_assoc, ← zpow_sub₀, hrounded, mul_assoc] using hmyround
  have isRounded : fmt.toFloatFormat.IsRounded (ofSign s * (fmant * 2 ^ fexp)) := by
    apply FloatFormat.IsRounded.simpleSign_mul
    rw [hfmant]
    refine .intro_le ?_ ?_
    · simp [hexp', Format.targetExponent]
    · simpa [CommonFormat.toFloatFormat]
  simp only [hmyround, ← hfmant, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast,
    NNReal.coe_zpow, NNReal.coe_ofNat, map_mul, SimpleSign.nnabs_coe, Real.nnabs_natCast, map_zpow₀,
    Real.nnabs_ofNat, one_mul]
  simp (disch := positivity) only [SimpleSign.ofValue_coe_mul_eq_self]
  split
  · rename_i hfmant'
    simp [hfmant']
  · simp (disch := positivity) [ofUnpackedFloat_finite, RealFloat.roundNNReal_eq_roundReal,
      RealFloat.roundReal_eq_of_isRounded isRounded, SimpleSign.ofValue_coe_mul_eq_self,
      RealFloat.ofValidReal, Real.toNNReal_mul, Real.toNNReal_zpow]

lemma ofUnpackedFloat_round {s : UnpackedFloat.Sign} {mant : ℕ} {exp : ℤ} (hmant : mant ≠ 0) :
    ofUnpackedFloat (UnpackedFloat.round fmt.toFormat s mant exp) =
      (.roundNNReal (ofSign s) (mant * 2 ^ exp) : RealFloat fmt.toFloatFormat) := by
  unfold UnpackedFloat.round
  extract_lets target
  split
  rename_i mant' exp' h
  have h₁ := decreaseExponent_eq h
  have hmant' : mant' ≠ 0 := by intro; simp_all [zpow_ne_zero]
  have hexp' : exp' ≤ fmt.toFormat.targetExponent (totalExponent mant' exp') := by
    unfold UnpackedFloat.decreaseExponent at h
    cases h
    simp [totalExponent, hmant]
    format_trivial
  rw [ofUnpackedFloat_roundWithAccuracy (f := 0) hmant' hexp' (.exact rfl), add_zero, decreaseExponent_eq h]

@[simp]
lemma ofUnpackedFloat_normalize (mant exp : ℤ) (zs : Float.Model.UnpackedFloat.Sign) :
    ofUnpackedFloat (UnpackedFloat.normalize fmt.toFormat mant exp zs) =
      (.roundReal (mant * 2 ^ exp) (ofSign zs) : RealFloat fmt.toFloatFormat) := by
  fun_cases UnpackedFloat.normalize
  · rename_i h
    rw [Int.compare_eq_lt] at h
    have : (-mant).toNat = mant.natAbs := by lia
    rw [ofUnpackedFloat_round (by simpa)]
    simp [RealFloat.roundReal_eq_roundNNReal, mul_neg_iff, zpow_pos, SimpleSign.ofValue_of_neg,
      map_mul, map_zpow₀, this, h]
  · rename_i h
    rw [Int.compare_eq_eq] at h
    simp [RealFloat.roundReal, h]
  · rename_i h
    rw [Int.compare_eq_gt] at h
    have : mant.toNat = mant.natAbs := by lia
    rw [ofUnpackedFloat_round (by simpa)]
    simp [RealFloat.roundReal_eq_roundNNReal, zpow_pos, SimpleSign.ofValue_of_pos,
      map_mul, map_zpow₀, this, h]

end LeanFloats.UnpackedFloat
