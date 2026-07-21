module
public import LeanFloats.UnpackedFloat.Valid

@[expose] public section

namespace LeanFloats.UnpackedFloat

open Float.Model

variable {fmt : CommonFormat}

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

@[simp]
lemma mantissa_ofMantissaAndAccuracy {n : Nat} {acc : UnpackedFloat.Accuracy} :
    (UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy n acc).mantissa = n := by
  fun_cases UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy <;> rfl

@[simp]
lemma mantissa_shiftRight {x : UnpackedFloat.ExtendedMantissa} {n : Nat} :
    (x >>> n).mantissa = x.mantissa >>> n := by
  change (Nat.repeat _ _ x).mantissa = _
  induction n <;> simp [*, Nat.repeat, UnpackedFloat.ExtendedMantissa.shiftRightOne, Nat.shiftRight_succ]

@[simp]
lemma shiftRight_zero {n : Nat} :
    { mantissa := 0, roundBit := false, stickyBit := false : UnpackedFloat.ExtendedMantissa } >>> n =
      { mantissa := 0, roundBit := false, stickyBit := false : UnpackedFloat.ExtendedMantissa } := by
  induction n with
  | zero => rfl
  | succ k ih => exact congrArg UnpackedFloat.ExtendedMantissa.shiftRightOne ih

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

lemma targetExponent_of_shiftToTargetExponent {fmt mant exp acc emant exp'}
    (hexp : exp ≤ fmt.targetExponent (totalExponent mant exp))
    (h : UnpackedFloat.shiftToTargetExponent fmt mant exp acc = (emant, exp')) :
    fmt.targetExponent (totalExponent emant.mantissa exp') = exp' := by
  cases h
  format_trivial

lemma mantissa_lt_of_shiftToTargetExponent {fmt mant exp acc emant exp'}
    (h : UnpackedFloat.shiftToTargetExponent fmt mant exp acc = (emant, exp')) :
    emant.mantissa < 2 ^ fmt.mantissaBits := by
  unfold UnpackedFloat.shiftToTargetExponent at h
  unfold UnpackedFloat.shiftToExponent at h
  cases h
  by_cases h : mant = 0
  · simp [h]
  simp only [mantissa_shiftRight, mantissa_ofMantissaAndAccuracy, Nat.shiftRight_eq_div_pow,
    Order.lt_two_iff, zero_le, pow_pos, Nat.div_lt_iff_lt_mul, ← Nat.pow_add,
    ← Nat.log2_lt h]
  format_trivial

lemma roundToNearestEven_ge {n acc} :
    n ≤ UnpackedFloat.Accuracy.roundToNearestEven n acc := by
  fun_cases UnpackedFloat.Accuracy.roundToNearestEven <;> grind

lemma roundToNearestEven_le_add_one {n acc} :
    UnpackedFloat.Accuracy.roundToNearestEven n acc ≤ n + 1 := by
  fun_cases UnpackedFloat.Accuracy.roundToNearestEven <;> grind

lemma targetExponent_mono {fmt : Format} {mant mant' exp} (h : mant ≤ mant') :
    fmt.targetExponent (totalExponent mant exp) ≤ fmt.targetExponent (totalExponent mant' exp) := by
  have : mant.log2 ≤ mant'.log2 := by
    simp only [Nat.log2_eq_log_two]
    exact Nat.log_mono (by decide) (by decide) h
  format_trivial

lemma shiftToTargetExponent_of_le {fmt mant exp emant exp'}
    (hmant : mant ≤ 2 ^ fmt.mantissaBits) (hexp : fmt.minExponent ≤ exp)
    (h : UnpackedFloat.shiftToTargetExponent fmt mant exp .exact = (emant, exp')) :
    (emant.mantissa * 2 ^ exp' : ℝ) = mant * 2 ^ exp := by
  by_cases heqz : mant = 0
  · simp_all [UnpackedFloat.shiftToTargetExponent, UnpackedFloat.shiftToExponent,
      UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy, eq_comm (b := emant)]
  have hemant : emant.mantissa = mant >>> (fmt.targetExponent (totalExponent mant exp) - exp).toNat := by
    symm at h; simp_all [UnpackedFloat.shiftToTargetExponent, UnpackedFloat.shiftToExponent]
  have hexp' := shiftToExponent_eq_max h
  rcases hmant.lt_or_eq with hlt | heq
  · rw [← Nat.log2_lt heqz] at hlt
    have : exp = exp' := by format_trivial
    simp only [← this, eq_comm (a := exp), sup_eq_left] at hexp'
    simp_all [Int.toNat_of_nonpos]
  · rw [← Int.cast_natCast]
    replace hexp' : exp' = exp + 1 := by format_trivial
    have : fmt.targetExponent (totalExponent mant exp) = exp + 1 := by format_trivial
    replace hemant : emant.mantissa = 2 ^ fmt.mantissaBitsWithoutImplicit := by
      rw [hemant, this]
      simp [heq, Format.mantissaBits, Nat.pow_add, Nat.shiftRight_one]
    simp [hemant, heq, hexp', Format.mantissaBits, pow_add,
      zpow_add_one₀, ← mul_assoc, mul_comm]

-- TODO: cleanup / simplify / split
lemma toUnboundedFloat_roundWithAccuracy {s : UnpackedFloat.Sign} {mant : ℕ} {exp : ℤ}
    {acc : UnpackedFloat.Accuracy} {f : NNReal}
    (hexp : exp ≤ fmt.toFormat.targetExponent (totalExponent mant exp))
    (hf : AccuracyRepresents acc f) :
    toUnboundedFloat (UnpackedFloat.roundWithAccuracy fmt.toFormat s mant exp acc) =
      (.roundNNReal (ofSign s) ((mant + f) * 2 ^ exp) : UnboundedFloat fmt.toFloatFormat) := by
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
  have hrounded_le : rounded ≤ 2 ^ (1 + fmt.mbits) :=
    roundToNearestEven_le_add_one.trans (mantissa_lt_of_shiftToTargetExponent h₁)
  replace hfmant : fmant * (2 : ℝ) ^ fexp = rounded * 2 ^ exp' :=
    shiftToTargetExponent_of_le (fmt := fmt.toFormat) hrounded_le (by format_trivial) h₂
  rw [UnboundedFloat.roundNNReal]
  unfold UnboundedFloat.roundReal
  extract_lets myexp myround
  have hmyexp : myexp = value_of% myexp := rfl
  have hmyround : myround = value_of% myround := rfl
  replace hmyexp : myexp = exp' := by
    simp only [hmyexp, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_zpow,
      NNReal.coe_ofNat, FloatFormat.getExponent_simpleSign_mul]
    rw [getExponent_eq_targetExponent _ hf.nonneg hf.lt_one, hexp']
    intro hmant
    have : mant.log2 = 0 := by simp [hmant]
    format_trivial
  replace hmyround : myround = ofSign s * (rounded * 2 ^ exp') := by
    rw [← Int.cast_natCast]
    simpa [hmyexp, mul_div_assoc, ← zpow_sub₀, hrounded, mul_assoc] using hmyround
  have isRounded : fmt.toFloatFormat.IsRounded (ofSign s * (fmant * 2 ^ fexp)) := by
    apply FloatFormat.IsRounded.simpleSign_mul
    rw [hfmant]
    refine .intro_le ?_ ?_
    · simp [hexp', Format.targetExponent]
    · simpa [CommonFormat.toFloatFormat, add_comm _ 1]
  simp only [hmyround, ← hfmant, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast,
    NNReal.coe_zpow, NNReal.coe_ofNat, map_mul, SimpleSign.nnabs_coe, Real.nnabs_natCast, map_zpow₀,
    Real.nnabs_ofNat, one_mul]
  simp (disch := positivity) only [SimpleSign.ofValue_coe_mul_eq_self]
  split
  · rename_i hfmant'
    simp [hfmant']
  · simp (disch := positivity) [toUnboundedFloat_finite, UnboundedFloat.roundNNReal_eq_roundReal,
      UnboundedFloat.roundReal_eq_ofValidReal isRounded, SimpleSign.ofValue_coe_mul_eq_self,
      UnboundedFloat.ofValidReal, Real.toNNReal_mul, Real.toNNReal_zpow]

lemma toUnboundedFloat_round {s : UnpackedFloat.Sign} {mant : ℕ} {exp : ℤ} (hmant : mant ≠ 0) :
    toUnboundedFloat (UnpackedFloat.round fmt.toFormat s mant exp) =
      (.roundNNReal (ofSign s) (mant * 2 ^ exp) : UnboundedFloat fmt.toFloatFormat) := by
  unfold UnpackedFloat.round
  extract_lets target
  split
  rename_i mant' exp' h
  have h₁ := decreaseExponent_eq h
  have hexp' : exp' ≤ fmt.toFormat.targetExponent (totalExponent mant' exp') := by
    unfold UnpackedFloat.decreaseExponent at h
    cases h
    simp [totalExponent, hmant]
    format_trivial
  rw [toUnboundedFloat_roundWithAccuracy (f := 0) hexp' (.exact rfl), add_zero, decreaseExponent_eq h]

@[simp]
lemma toUnboundedFloat_normalize (mant exp : ℤ) (zs : Float.Model.UnpackedFloat.Sign) :
    toUnboundedFloat (UnpackedFloat.normalize fmt.toFormat mant exp zs) =
      (.roundReal (mant * 2 ^ exp) (ofSign zs) : UnboundedFloat fmt.toFloatFormat) := by
  fun_cases UnpackedFloat.normalize
  · rename_i h
    rw [Int.compare_eq_lt] at h
    have : (-mant).toNat = mant.natAbs := by lia
    rw [toUnboundedFloat_round (by simpa)]
    simp [UnboundedFloat.roundReal_eq_roundNNReal, mul_neg_iff, zpow_pos, SimpleSign.ofValue_of_neg,
      map_mul, map_zpow₀, this, h]
  · rename_i h
    rw [Int.compare_eq_eq] at h
    simp [UnboundedFloat.roundReal, h]
  · rename_i h
    rw [Int.compare_eq_gt] at h
    have : mant.toNat = mant.natAbs := by lia
    rw [toUnboundedFloat_round (by simpa)]
    simp [UnboundedFloat.roundReal_eq_roundNNReal, zpow_pos, SimpleSign.ofValue_of_pos,
      map_mul, map_zpow₀, this, h]

theorem isRounded_roundWithAccuracy {fmt : Format}
    {s : UnpackedFloat.Sign} {mant : ℕ} {exp : ℤ} {acc : UnpackedFloat.Accuracy}
    (hexp : exp ≤ fmt.targetExponent (totalExponent mant exp)) :
    IsRounded fmt (UnpackedFloat.roundWithAccuracy fmt s mant exp acc) := by
  unfold UnpackedFloat.roundWithAccuracy
  split
  rename_i emant exp' h₁
  extract_lets rounded
  split
  rename_i femant fexp h₂
  extract_lets fmant
  split
  · constructor
  have hexp' := shiftToExponent_eq_max h₁
  have hfexp := shiftToExponent_eq_max h₂
  have hfmant₁ := mantissa_lt_of_shiftToTargetExponent h₂
  have hfmant := shiftToTargetExponent_of_le
    (roundToNearestEven_le_add_one.trans (mantissa_lt_of_shiftToTargetExponent h₁))
    (by format_trivial) h₂
  change fmant * (2 : ℝ) ^ fexp = rounded * 2 ^ exp' at hfmant
  have := targetExponent_of_shiftToTargetExponent hexp h₁
  have : exp' ≤ fmt.targetExponent (totalExponent emant.roundedMantissa exp') :=
    this.symm.trans_le (targetExponent_mono roundToNearestEven_ge)
  constructor
  rw [targetExponent_of_shiftToTargetExponent _ h₂]
  format_trivial

theorem isRounded_round {fmt : Format} {s : UnpackedFloat.Sign} {mant : ℕ} {exp : ℤ}
    (hmant : mant ≠ 0) : IsRounded fmt (UnpackedFloat.round fmt s mant exp) := by
  unfold UnpackedFloat.round
  simp only [UnpackedFloat.decreaseExponent, Int.ofNat_toNat]
  apply isRounded_roundWithAccuracy
  simp [totalExponent]
  simp [hmant]; format_trivial

@[simp]
theorem isRounded_normalize {fmt : Format} {s : UnpackedFloat.Sign} {mant : ℤ} {exp : ℤ} :
    IsRounded fmt (UnpackedFloat.normalize fmt mant exp s) := by
  unfold UnpackedFloat.normalize
  split <;> simp_all [isRounded_round, compare_lt_iff_lt, compare_gt_iff_gt]

end LeanFloats.UnpackedFloat
