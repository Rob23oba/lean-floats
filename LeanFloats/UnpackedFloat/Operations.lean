module
public import LeanFloats.UnpackedFloat.Valid
public import LeanFloats.UnpackedFloat.Rounding

namespace LeanFloats.UnpackedFloat

open Float.Model

variable {fmt : CommonFormat}

lemma toUnboundedFloat_add {fmt fmt' common}
    [HasCommonOfFormat fmt common] [HasCommonOfFloatFormat fmt' common]
    {x y : UnpackedFloat}
    (hx : IsRounded fmt x) (hy : IsRounded fmt y) :
    toUnboundedFloat (.add fmt x y) =
      (toUnboundedFloat x : UnboundedFloat fmt').add (toUnboundedFloat y) := by
  cases HasCommonOfFormat.elim fmt
  cases HasCommonOfFloatFormat.elim fmt'
  fun_cases UnpackedFloat.add
  · simp
  · simp
  · simp_all
  · simp_all [UnboundedFloat.infinity_add_infinity]
  · cases y <;> simp_all [toUnboundedFloat_finite_of_isRounded]
  · cases x <;> simp_all [toUnboundedFloat_finite_of_isRounded]
  · rename_i s s' _; cases s' <;>
      simp_all [← UnboundedFloat.zero_eq_ofValidNNReal, UnboundedFloat.ofValidNNReal_neg_one_eq_neg_zero]
  · rename_i s s' _; cases s <;> cases s' <;>
      simp_all [← UnboundedFloat.zero_eq_ofValidNNReal, UnboundedFloat.ofValidNNReal_neg_one_eq_neg_zero]
  · rename_i s _ _ _
    cases s <;> cases y <;>
      simp_all [← UnboundedFloat.zero_eq_ofValidNNReal, UnboundedFloat.ofValidNNReal_neg_one_eq_neg_zero,
        UnboundedFloat.zero_add_eq_ite, toUnboundedFloat_finite_of_isRounded, ne_of_gt]
  · rename_i s _ _ _
    cases s <;> cases x <;>
      simp_all [← UnboundedFloat.zero_eq_ofValidNNReal, UnboundedFloat.ofValidNNReal_neg_one_eq_neg_zero,
        UnboundedFloat.add_zero_eq_ite, toUnboundedFloat_finite_of_isRounded, ne_of_gt]
  · rename_i s m e hm s₂ m₂ e₂ hm₂ emin m₃ e₃ h₁ m₄ e₄ h₂ m₅
    have hm₃ := decreaseExponent_eq_min h₁
    have he₃ := decreaseExponent_eq h₁
    have hm₄ := decreaseExponent_eq_min h₂
    have he₄ := decreaseExponent_eq h₂
    have hm₄_pos : 0 < m₄ := by by_contra! heq; simp_all [zpow_ne_zero, hm₂.ne']
    simp +contextual [toUnboundedFloat_finite_of_isRounded, m₅, add_mul, mul_assoc, emin, UnboundedFloat.add,
      ← not_imp_not (a := _ ∨ _), SimpleSign.ne_iff_eq_neg, ← neg_add_rev, *]
    simp (disch := positivity) [ne_of_gt]

lemma isRounded_add {fmt : Format} {x y : UnpackedFloat}
    (hx : IsRounded fmt x) (hy : IsRounded fmt y) : IsRounded fmt (.add fmt x y) := by
  cases x <;> cases y <;> simp [UnpackedFloat.add] <;> (try split) <;> simp_all

@[simp]
lemma toUnboundedFloat_neg {fmt : FloatFormat 2} (x : UnpackedFloat) :
    toUnboundedFloat x.neg = -(toUnboundedFloat x : UnboundedFloat fmt) := by
  fun_cases toUnboundedFloat <;> simp [UnpackedFloat.neg, toUnboundedFloat_finite]

@[simp]
lemma toUnboundedFloat_abs {fmt : FloatFormat 2} (x : UnpackedFloat) :
    toUnboundedFloat x.abs = (toUnboundedFloat x : UnboundedFloat fmt).abs := by
  fun_cases toUnboundedFloat <;> simp [UnpackedFloat.abs, toUnboundedFloat_finite]

@[simp]
lemma sub_eq_add_neg (x y : UnpackedFloat) (fmt : Format) : x.sub fmt y = x.add fmt y.neg := by
  cases x <;> cases y <;> simp [UnpackedFloat.add, UnpackedFloat.neg, UnpackedFloat.sub, Int.add_neg_eq_sub]

lemma toUnboundedFloat_sub {x y : UnpackedFloat}
    (hx : IsRounded fmt.toFormat x) (hy : IsRounded fmt.toFormat y) :
    toUnboundedFloat (.sub fmt.toFormat x y) =
      (toUnboundedFloat x : UnboundedFloat fmt.toFloatFormat).sub (toUnboundedFloat y) := by
  simp [sub_eq_add_neg, toUnboundedFloat_add, hx, hy.neg]

lemma toUnboundedFloat_mul {fmt fmt' common}
    [HasCommonOfFormat fmt common] [HasCommonOfFloatFormat fmt' common]
    {x y : UnpackedFloat}
    (hx : IsRounded fmt x) (hy : IsRounded fmt y) :
    toUnboundedFloat (.mul fmt x y) =
      (toUnboundedFloat x : UnboundedFloat fmt').mul (toUnboundedFloat y) := by
  cases HasCommonOfFormat.elim fmt
  cases HasCommonOfFloatFormat.elim fmt'
  fun_cases UnpackedFloat.mul
  · simp
  · simp
  · simp
  · simp_all [UnboundedFloat.infinity_mul_ofValidNNReal, toUnboundedFloat_finite_of_isRounded, ne_of_gt]
  · simp_all [UnboundedFloat.ofValidNNReal_mul_infinity, toUnboundedFloat_finite_of_isRounded, ne_of_gt]
  · simp [UnboundedFloat.infinity_mul_ofValidNNReal]
  · simp [UnboundedFloat.ofValidNNReal_mul_infinity]
  · simp_all -implicitDefEqProofs [UnboundedFloat.ofValidNNReal_mul_ofValidNNReal, toUnboundedFloat_finite_of_isRounded,
      UnboundedFloat.roundNNReal_eq_ofValidNNReal]
  · simp_all -implicitDefEqProofs [UnboundedFloat.ofValidNNReal_mul_ofValidNNReal, toUnboundedFloat_finite_of_isRounded,
      UnboundedFloat.roundNNReal_eq_ofValidNNReal]
  · simp_all -implicitDefEqProofs [UnboundedFloat.ofValidNNReal_mul_ofValidNNReal,
      UnboundedFloat.roundNNReal_eq_ofValidNNReal]
  · rename_i s m e hm s₂ m₂ e₂ hm₂
    rw [toUnboundedFloat_roundWithAccuracy (f := 0) _ (.exact rfl)]
    · simp [toUnboundedFloat_finite_of_isRounded, UnboundedFloat.ofValidNNReal_mul_ofValidNNReal,
        zpow_add₀, mul_assoc, mul_left_comm, *]
    · rcases hx with _ | _ | _ | ⟨-, hx⟩
      rcases hy with _ | _ | _ | ⟨-, hy⟩
      have := Nat.log2_add_log2_le_log2_mul hm.ne' hm₂.ne'
      simp +zetaDelta only [Format.targetExponent, totalExponent, Format.mantissaBits, Nat.cast_add,
        Nat.cast_one, Format.minExponent, le_sup_iff] at *
      have : 0 < 2 ^ (common.ebits - 1) := by simp
      lia

lemma isRounded_mul {fmt common} [HasCommonOfFormat fmt common] {x y : UnpackedFloat}
    (hx : IsRounded fmt x) (hy : IsRounded fmt y) : IsRounded fmt (.mul fmt x y) := by
  cases HasCommonOfFormat.elim fmt
  cases x <;> cases y <;> (try simp [UnpackedFloat.mul]; done)
  rename_i s m e hm s' m₂ e₂ hm₂
  rcases hx with _ | _ | _ | ⟨-, hx⟩
  rcases hy with _ | _ | _ | ⟨-, hy⟩
  have := Nat.log2_add_log2_le_log2_mul hm.ne' hm₂.ne'
  apply isRounded_roundWithAccuracy
  have : 0 < 2 ^ (common.ebits - 1) := by simp
  simp +zetaDelta only [Format.targetExponent, totalExponent, Format.mantissaBits, Nat.cast_add,
    Nat.cast_one, Format.minExponent, le_sup_iff] at *
  lia

lemma accuracyRepresents_accuracyOfFraction {n d : ℕ} (h : n < d) :
    AccuracyRepresents (UnpackedFloat.accuracyOfFraction n d) (n / d) := by
  rw [UnpackedFloat.accuracyOfFraction]
  split
  · constructor
    simp [*]
  · have hd : 0 < d := by lia
    constructor
    · positivity
    · simp [div_lt_iff₀, hd, h]
    · rcases lt_trichotomy (2 * n) d with h | h | h <;>
        simp [compare_lt_iff_lt.mpr, compare_gt_iff_gt.mpr, h,
          compare_lt_iff_lt, compare_gt_iff_gt] <;>
        field_simp <;> norm_cast <;> simp_all [mul_comm]

lemma divCore_spec {m₁ m₂ : ℕ} {e₁ e₂ : ℤ} {mant exp acc} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (h : UnpackedFloat.divCore fmt.toFormat m₁ e₁ m₂ e₂ = (mant, exp, acc)) :
    exp ≤ fmt.toFormat.targetExponent (totalExponent mant exp) ∧
      AccuracyRepresents acc (m₁ * 2 ^ e₁ / (m₂ * 2 ^ e₂) / 2 ^ exp - mant) := by
  unfold UnpackedFloat.divCore at h
  extract_lets target shift shifted at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  constructor
  · have := Nat.log2_sub_log2_le_log2_div_add_one hm₂.ne' shifted
    simp [shifted, Nat.log2_shiftLeft hm₁.ne'] at this
    format_trivial
  · convert accuracyRepresents_accuracyOfFraction (Nat.mod_lt shifted hm₂)
    rw [← Int.cast_natCast (shifted % m₂), Int.natCast_mod,
        eq_sub_of_add_eq (Int.emod_add_mul_ediv _ _)]
    simp only [← Int.natCast_ediv, Int.cast_sub, Int.cast_natCast, Int.cast_mul]
    have : target ≤ e₁ - e₂ := by simp [target]
    simp [sub_div, hm₂.ne', shifted, shift, Nat.shiftLeft_eq, ← zpow_natCast,
      this, zpow_sub₀, ← div_div, div_right_comm, ← mul_div_assoc]

lemma toUnboundedFloat_div {fmt fmt' common}
    [HasCommonOfFormat fmt common] [HasCommonOfFloatFormat fmt' common]
    {x y : UnpackedFloat}
    (hx : IsRounded fmt x) (hy : IsRounded fmt y) :
    toUnboundedFloat (.div fmt x y) =
      (toUnboundedFloat x : UnboundedFloat fmt').div (toUnboundedFloat y) := by
  cases HasCommonOfFormat.elim fmt
  cases HasCommonOfFloatFormat.elim fmt'
  fun_cases UnpackedFloat.div
  · simp
  · simp
  · simp
  · simp [toUnboundedFloat_finite_of_isRounded, *]
  · simp [toUnboundedFloat_finite_of_isRounded, UnboundedFloat.ofValidNNReal_div_infinity, *]
  · simp
  · simp [UnboundedFloat.ofValidNNReal_div_infinity]
  · simp [toUnboundedFloat_finite_of_isRounded, UnboundedFloat.ofValidNNReal_div_ofValidNNReal, ne_of_gt, *]
  · simp -implicitDefEqProofs [toUnboundedFloat_finite_of_isRounded, UnboundedFloat.ofValidNNReal_div_ofValidNNReal,
      UnboundedFloat.roundNNReal_eq_ofValidNNReal, ne_of_gt, *]
  · simp [UnboundedFloat.ofValidNNReal_div_ofValidNNReal]
  · rename_i s m e hm s₂ m₂ e₂ hm₂ m' e' acc' h
    have ⟨h₁, h₂⟩ := divCore_spec hm hm₂ h
    rw [toUnboundedFloat_roundWithAccuracy (f := NNReal.mk _ h₂.nonneg) h₁ h₂]
    simp [toUnboundedFloat_finite_of_isRounded, UnboundedFloat.ofValidNNReal_div_ofValidNNReal, hm₂.ne',
      UnboundedFloat.roundNNReal_eq_roundReal, *]

lemma isRounded_div {fmt common} [HasCommonOfFormat fmt common] {x y : UnpackedFloat} :
    IsRounded fmt (.div fmt x y) := by
  cases HasCommonOfFormat.elim fmt
  fun_cases UnpackedFloat.div <;> try simp
  rename_i s m e hm s' m₂ e₂ hm₂ m' e' acc' h
  have ⟨h₁, _⟩ := divCore_spec hm hm₂ h
  exact isRounded_roundWithAccuracy h₁

lemma accuracyRepresents_sqrt (m : ℕ) :
    letI root := Nat.sqrt m
    letI rem := m - root * root
    letI accuracy : UnpackedFloat.Accuracy := if rem = 0 then .exact else .inexact (if rem ≤ root then .lt else .gt)
    AccuracyRepresents accuracy (√m - root) := by
  rify
  rw [Nat.cast_sub m.sqrt_le]
  simp only [Nat.cast_mul, sub_eq_zero, Nat.cast_nonneg,
    ← Real.sqrt_eq_iff_mul_self_eq, tsub_le_iff_right]
  have sqrt_le : m.sqrt ≤ √m := Real.le_sqrt_of_sq_le (mod_cast m.sqrt_le')
  split
  · simp_all [AccuracyRepresents.exact]
  · rename_i h₁
    have pos : 0 < √m - m.sqrt :=
      lt_of_le_of_ne (sub_nonneg_of_le sqrt_le) (sub_ne_zero.mpr h₁).symm
    have lt_one : √m - m.sqrt < 1 := by
      rw [sub_lt_iff_lt_add, Real.sqrt_lt (by positivity) (by positivity), add_comm 1]
      exact mod_cast m.lt_succ_sqrt'
    split
    · rename_i h₂
      refine .inexact pos lt_one ?_
      rw [compare_lt_iff_lt, sub_lt_iff_lt_add, Real.sqrt_lt (by positivity) (by positivity)]
      linarith
    · rename_i h₂
      rw [not_le] at h₂
      norm_cast at h₂
      rw [Nat.lt_iff_add_one_le] at h₂
      rify at h₂
      refine .inexact pos lt_one ?_
      rw [compare_gt_iff_gt, lt_sub_iff_add_lt, Real.lt_sqrt (by positivity)]
      linarith

lemma sqrtCore_spec {m : ℕ} {e : ℤ} {mant exp acc} (hm : 0 < m)
    (h : UnpackedFloat.sqrtCore fmt.toFormat m e = (mant, exp, acc)) :
    exp ≤ fmt.toFormat.targetExponent (totalExponent mant exp) ∧
      AccuracyRepresents acc (√(m * 2^e) / 2 ^ exp - mant) := by
  unfold UnpackedFloat.sqrtCore at h
  extract_lets target shift shifted root rem acc at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  constructor
  · simp +zetaDelta [totalExponent, Format.targetExponent, Format.minExponent,
      Nat.log2_shiftLeft, hm.ne']
    lia
  · convert accuracyRepresents_sqrt shifted
    have : 2 * target ≤ e := by simp [target]; lia
    simp [shifted, Nat.shiftLeft_eq, shift, pow_toNat_eq_zpow, this, zpow_sub₀,
      zpow_mul', zpow_two, mul_div_assoc]

lemma toUnboundedFloat_sqrt {fmt fmt' common}
    [HasCommonOfFormat fmt common] [HasCommonOfFloatFormat fmt' common]
    {x : UnpackedFloat} (hx : IsRounded fmt x) :
    toUnboundedFloat (.sqrt fmt x) = (toUnboundedFloat x : UnboundedFloat fmt').sqrt := by
  cases HasCommonOfFormat.elim fmt
  cases HasCommonOfFloatFormat.elim fmt'
  fun_cases UnpackedFloat.sqrt
  · simp
  · simp
  · simp
  · simp [toUnboundedFloat_finite_of_isRounded, UnboundedFloat.sqrt_ofValidNNReal_neg_one, ne_of_gt, *]
  · simp [UnboundedFloat.sqrt_ofValidNNReal, UnboundedFloat.roundReal_eq_ofValidReal, UnboundedFloat.ofValidReal, *]
  · rename_i m e hm m' e' acc' h
    have ⟨h₁, h₂⟩ := sqrtCore_spec hm h
    rw [toUnboundedFloat_roundWithAccuracy (f := NNReal.mk _ h₂.nonneg) h₁ h₂]
    simp [toUnboundedFloat_finite_of_isRounded, UnboundedFloat.sqrt_ofValidNNReal_one,
      UnboundedFloat.roundNNReal_eq_roundReal, *]

lemma isRounded_sqrt {fmt common} [HasCommonOfFormat fmt common]
    {x : UnpackedFloat} : IsRounded fmt (.sqrt fmt x) := by
  cases HasCommonOfFormat.elim fmt
  fun_cases UnpackedFloat.sqrt <;> try simp
  rename_i m e hm m' e' acc' h
  have ⟨h₁, _⟩ := sqrtCore_spec hm h
  exact isRounded_roundWithAccuracy h₁

lemma compare_eq_compare_toUnboundedFloat {fmt common}
    [HasCommonOfFormat fmt common] {x y : UnpackedFloat} (hx : IsRounded fmt x) (hy : IsRounded fmt y) :
    x.compare y = (toUnboundedFloat x).compare (toUnboundedFloat y : UnboundedFloat common.toFloatFormat) := by
  cases HasCommonOfFormat.elim fmt
  fun_cases UnpackedFloat.compare
  · simp
  · simp
  · clear hx; clear hy; simp; decide +revert
  · cases y <;> simp_all [toUnboundedFloat_finite_of_isRounded]
  · cases y <;> simp_all [toUnboundedFloat_finite_of_isRounded]
  · cases x <;> simp_all [toUnboundedFloat_finite_of_isRounded]
  · cases x <;> simp_all [toUnboundedFloat_finite_of_isRounded]
  · simp [eq_comm (a := some Ordering.gt), toUnboundedFloat_finite_of_isRounded,
      Std.compare_eq_gt, *]
  · simp [eq_comm (a := some Ordering.lt), toUnboundedFloat_finite_of_isRounded,
      Std.compare_eq_lt, *]
  · simp [eq_comm (a := some Ordering.lt), toUnboundedFloat_finite_of_isRounded,
      Std.compare_eq_lt, *]
  · simp [eq_comm (a := some Ordering.gt), toUnboundedFloat_finite_of_isRounded,
      Std.compare_eq_gt, *]
  · simp
  · simp only [hx, toUnboundedFloat_finite_of_isRounded, ofSign_negative, hy,
      UnboundedFloat.compare_ofValidNNReal_ofValidNNReal, SimpleSign.coe_neg_one,
      neg_mul, one_mul, Option.some.injEq, compare_neg, Ordering.swap_then,
      ← Std.OrientedOrd.eq_swap]
    rw [(isRounded_of_isRounded_finite hy).compare_eq_of_nonneg
      (isRounded_of_isRounded_finite hx) (by positivity) (by positivity)]
    simp [getMantissa_of_isRounded_finite hx, getMantissa_of_isRounded_finite hy,
      getExponent_of_isRounded_finite hx, getExponent_of_isRounded_finite hy]
  · simp [eq_comm (a := some Ordering.lt), toUnboundedFloat_finite_of_isRounded,
      Std.compare_eq_lt, lt_trans (b := (0 : ℝ)), *]
  · simp [eq_comm (a := some Ordering.gt), toUnboundedFloat_finite_of_isRounded,
      Std.compare_eq_gt, lt_trans (b := (0 : ℝ)), *]
  · simp only [hx, toUnboundedFloat_finite_of_isRounded, ofSign_positive, hy,
      UnboundedFloat.compare_ofValidNNReal_ofValidNNReal, SimpleSign.coe_one, one_mul,
      Option.some.injEq]
    rw [(isRounded_of_isRounded_finite hx).compare_eq_of_nonneg
      (isRounded_of_isRounded_finite hy) (by positivity) (by positivity)]
    simp [getMantissa_of_isRounded_finite hx, getMantissa_of_isRounded_finite hy,
      getExponent_of_isRounded_finite hx, getExponent_of_isRounded_finite hy]

lemma le_eq_toUnboundedFloat_le {fmt common} [HasCommonOfFormat fmt common]
    {x y : UnpackedFloat} (hx : IsRounded fmt x) (hy : IsRounded fmt y) :
    x.le y = decide (toUnboundedFloat x ≤ (toUnboundedFloat y : UnboundedFloat common.toFloatFormat)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, UnpackedFloat.le,
    compare_eq_compare_toUnboundedFloat hx hy, ← UnboundedFloat.any_isLE_compare_iff]

lemma lt_eq_toUnboundedFloat_lt {fmt common} [HasCommonOfFormat fmt common]
    {x y : UnpackedFloat} (hx : IsRounded fmt x) (hy : IsRounded fmt y) :
    x.lt y = decide (toUnboundedFloat x < (toUnboundedFloat y : UnboundedFloat common.toFloatFormat)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, UnpackedFloat.lt, beq_iff_eq,
    compare_eq_compare_toUnboundedFloat hx hy, ← UnboundedFloat.compare_eq_some_lt_iff]

lemma beq_eq_toUnboundedFloat_equiv {fmt common} [HasCommonOfFormat fmt common]
    {x y : UnpackedFloat} (hx : IsRounded fmt x) (hy : IsRounded fmt y) :
    x.beq y = decide (toUnboundedFloat x ≈ (toUnboundedFloat y : UnboundedFloat common.toFloatFormat)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, UnpackedFloat.beq, beq_iff_eq,
    compare_eq_compare_toUnboundedFloat hx hy, ← UnboundedFloat.compare_eq_some_eq_iff]

lemma toInt_eq {fmt common} [HasCommonOfFormat fmt common]
    {x : UnpackedFloat} (hx : IsRounded fmt x) (negInf posInf : ℤ) :
    x.toInt negInf posInf =
      match (toUnboundedFloat x : UnboundedFloat common.toFloatFormat) with
      | .ofValidNNReal s x _h => s * ⌊x⌋₊
      | .infinity 1 => posInf
      | .infinity (-1) => negInf
      | .nan => 0 := by
  cases HasCommonOfFormat.elim fmt
  fun_cases UnpackedFloat.toInt
  · simp
  · simp
  · simp
  · simp
  · simp only [toUnboundedFloat_finite_of_isRounded hx]
    unfold UnpackedFloat.roundToInt; split; split
    rename_i s m e hm _ mant' exp' h₁ _ femant fexp h₂
    symm at h₁ h₂
    cases e using Int.negInduction <;> norm_cast <;>
      simp_all [UnpackedFloat.decreaseExponent, UnpackedFloat.shiftToExponent,
        Nat.shiftLeft_eq, -Nat.cast_mul, ← div_eq_mul_inv, Nat.floor_div_two_pow]

lemma toNat_toInt_eq {fmt common} [HasCommonOfFormat fmt common]
    {x : UnpackedFloat} (hx : IsValid fmt x) (posInf : ℕ)
    (h : posInf ≤ 1 <<< fmt.infinityExponent := by assumption) :
    min (x.toInt 0 posInf).toNat posInf =
      min ⌊(RealFloat.ofUnbounded
        (toUnboundedFloat x : UnboundedFloat common.toFloatFormat)).toReal⌋₊ posInf := by
  rw [Nat.shiftLeft_eq] at h
  cases HasCommonOfFormat.elim fmt
  rw [toInt_eq hx.isRounded]
  split
  · rename_i s x h _
    cases s <;> simp_all [isValid_iff_isRounded_and_inRange,
      RealFloat.ofUnbounded_eq_ofUnboundedInRange, Nat.floor_of_nonpos]
  · simp [*]; norm_cast; simpa [-Nat.cast_pow] using h
  · simp [Nat.floor_of_nonpos, *]
  · simp [*]

lemma max_min_toInt_eq {fmt common} [HasCommonOfFormat fmt common]
    {x : UnpackedFloat} (hx : IsValid fmt x) (negInf posInf : ℤ)
    (hneg : negInf < 0 := by simp) (hpos : 0 < posInf := by simp)
    (hp : posInf ≤ 1 <<< fmt.infinityExponent := by norm_cast)
    (hn : -1 <<< fmt.infinityExponent ≤ negInf := by norm_cast) :
    max negInf (min posInf (x.toInt negInf posInf)) =
      max negInf (min posInf (RoundingFunction.towardsZero (RealFloat.ofUnbounded
        (toUnboundedFloat x : UnboundedFloat common.toFloatFormat)).toReal)) := by
  rw [Nat.shiftLeft_eq] at hp hn
  cases HasCommonOfFormat.elim fmt
  rw [toInt_eq hx.isRounded]
  have : negInf ≤ posInf := by lia
  have : ¬ posInf ≤ negInf := by lia
  split
  · rename_i s x h _
    cases s <;> simp_all [isValid_iff_isRounded_and_inRange,
      RealFloat.ofUnbounded_eq_ofUnboundedInRange, RoundingFunction.balanced_apply_of_nonneg]
  · simp [*]; norm_cast; simpa [-Nat.cast_pow, max_min_distrib_left, *] using hp
  · simp [*]; norm_cast; simpa [-Nat.cast_pow, hneg.le, *] using hn
  · simp [*]

lemma toUInt8_eq {fmt common} [HasCommonOfFormat fmt common]
    {x : UnpackedFloat} (hx : IsValid fmt x)
    (h : 0xFF ≤ 1 <<< fmt.infinityExponent := by decide) :
    x.toUInt8 = UInt8.ofNatClamp
      ⌊(RealFloat.ofUnbounded (toUnboundedFloat x : UnboundedFloat common.toFloatFormat)).toReal⌋₊ := by
  simpa [UnpackedFloat.toUInt8, ← UInt8.toNat_inj, UInt8.toNat_ofNatClamp] using toNat_toInt_eq hx 0xFF

lemma toUInt16_eq {fmt common} [HasCommonOfFormat fmt common]
    {x : UnpackedFloat} (hx : IsValid fmt x)
    (h : 0xFFFF ≤ 1 <<< fmt.infinityExponent := by decide) :
    x.toUInt16 = UInt16.ofNatClamp
      ⌊(RealFloat.ofUnbounded (toUnboundedFloat x : UnboundedFloat common.toFloatFormat)).toReal⌋₊ := by
  simpa [UnpackedFloat.toUInt16, ← UInt16.toNat_inj, UInt16.toNat_ofNatClamp] using toNat_toInt_eq hx 0xFFFF

lemma toUInt32_eq {fmt common} [HasCommonOfFormat fmt common]
    {x : UnpackedFloat} (hx : IsValid fmt x)
    (h : 0xFFFF_FFFF ≤ 1 <<< fmt.infinityExponent := by decide) :
    x.toUInt32 = UInt32.ofNatClamp
      ⌊(RealFloat.ofUnbounded (toUnboundedFloat x : UnboundedFloat common.toFloatFormat)).toReal⌋₊ := by
  simpa [UnpackedFloat.toUInt32, ← UInt32.toNat_inj, UInt32.toNat_ofNatClamp] using toNat_toInt_eq hx 0xFFFF_FFFF

lemma toUInt64_eq {fmt common} [HasCommonOfFormat fmt common]
    {x : UnpackedFloat} (hx : IsValid fmt x)
    (h : 0xFFFF_FFFF_FFFF_FFFF ≤ 1 <<< fmt.infinityExponent := by decide) :
    x.toUInt64 = UInt64.ofNatClamp
      ⌊(RealFloat.ofUnbounded (toUnboundedFloat x : UnboundedFloat common.toFloatFormat)).toReal⌋₊ := by
  simpa [UnpackedFloat.toUInt64, ← UInt64.toNat_inj, UInt64.toNat_ofNatClamp] using toNat_toInt_eq hx 0xFFFF_FFFF_FFFF_FFFF

lemma toUSize_eq {fmt common} [HasCommonOfFormat fmt common]
    {x : UnpackedFloat} (hx : IsValid fmt x)
    (h : 0xFFFF_FFFF_FFFF_FFFF ≤ 1 <<< fmt.infinityExponent := by decide) :
    x.toUSize = USize.ofNatClamp
      ⌊(RealFloat.ofUnbounded (toUnboundedFloat x : UnboundedFloat common.toFloatFormat)).toReal⌋₊ := by
  simpa [UnpackedFloat.toUSize, ← USize.toNat_inj, USize.toNat_ofNatClamp]
    using toNat_toInt_eq hx (USize.size - 1) (le_trans (Nat.pred_le_pred USize.size_le) h)

lemma toInt8_eq {fmt common} [HasCommonOfFormat fmt common]
    {x : UnpackedFloat} (hx : IsValid fmt x)
    (hp : 0x7f ≤ 1 <<< fmt.infinityExponent := by decide)
    (hn : -(1 <<< fmt.infinityExponent : ℤ) ≤ -0x80 := by decide) :
    x.toInt8 = Int8.ofIntClamp
      (RoundingFunction.towardsZero (RealFloat.ofUnbounded (toUnboundedFloat x : UnboundedFloat common.toFloatFormat)).toReal) := by
  simpa [UnpackedFloat.toInt8, ← Int8.toInt_inj, Int8.toInt_ofIntClamp_eq_max, Int8.maxValue] using max_min_toInt_eq hx (-0x80) 0x7f

lemma toInt16_eq {fmt common} [HasCommonOfFormat fmt common]
    {x : UnpackedFloat} (hx : IsValid fmt x)
    (hp : 0x7fff ≤ 1 <<< fmt.infinityExponent := by decide)
    (hn : -(1 <<< fmt.infinityExponent : ℤ) ≤ -0x8000 := by decide) :
    x.toInt16 = Int16.ofIntClamp
      (RoundingFunction.towardsZero (RealFloat.ofUnbounded (toUnboundedFloat x : UnboundedFloat common.toFloatFormat)).toReal) := by
  simpa [UnpackedFloat.toInt16, ← Int16.toInt_inj, Int16.toInt_ofIntClamp_eq_max, Int16.maxValue] using max_min_toInt_eq hx (-0x8000) 0x7fff

lemma toInt32_eq {fmt common} [HasCommonOfFormat fmt common]
    {x : UnpackedFloat} (hx : IsValid fmt x)
    (hp : 0x7fff_ffff ≤ 1 <<< fmt.infinityExponent := by decide)
    (hn : -(1 <<< fmt.infinityExponent : ℤ) ≤ -0x8000_0000 := by decide) :
    x.toInt32 = Int32.ofIntClamp
      (RoundingFunction.towardsZero (RealFloat.ofUnbounded (toUnboundedFloat x : UnboundedFloat common.toFloatFormat)).toReal) := by
  simpa [UnpackedFloat.toInt32, ← Int32.toInt_inj, Int32.toInt_ofIntClamp_eq_max, Int32.maxValue] using max_min_toInt_eq hx (-0x8000_0000) 0x7fff_ffff

lemma toInt64_eq {fmt common} [HasCommonOfFormat fmt common]
    {x : UnpackedFloat} (hx : IsValid fmt x)
    (hp : 0x7fff_ffff_ffff_ffff ≤ 1 <<< fmt.infinityExponent := by decide)
    (hn : -(1 <<< fmt.infinityExponent : ℤ) ≤ -0x8000_0000_0000_0000 := by decide) :
    x.toInt64 = Int64.ofIntClamp
      (RoundingFunction.towardsZero (RealFloat.ofUnbounded (toUnboundedFloat x : UnboundedFloat common.toFloatFormat)).toReal) := by
  simpa [UnpackedFloat.toInt64, ← Int64.toInt_inj, Int64.toInt_ofIntClamp_eq_max, Int64.maxValue]
    using max_min_toInt_eq hx (-0x8000_0000_0000_0000) 0x7fff_ffff_ffff_ffff

lemma toISize_eq {fmt common} [HasCommonOfFormat fmt common]
    {x : UnpackedFloat} (hx : IsValid fmt x)
    (hp : 0x7fff_ffff_ffff_ffff ≤ 1 <<< fmt.infinityExponent := by decide)
    (hn : -(1 <<< fmt.infinityExponent : ℤ) ≤ -0x8000_0000_0000_0000 := by decide) :
    x.toISize = ISize.ofIntClamp
      (RoundingFunction.towardsZero (RealFloat.ofUnbounded (toUnboundedFloat x : UnboundedFloat common.toFloatFormat)).toReal) := by
  simpa [UnpackedFloat.toISize, ← ISize.toInt_inj, ISize.toInt_ofIntClamp_eq_max, ISize.maxValue]
    using max_min_toInt_eq hx ISize.minValue.toInt ISize.maxValue.toInt
      ISize.toInt_minValue_lt_zero (lt_of_lt_of_le (by decide) ISize.le_toInt_maxValue)
      (le_trans (ISize.toInt_le_int64MaxValue _) (Nat.cast_le.mpr hp))
      (le_trans hn (ISize.int64MinValue_le_toInt _))

end UnpackedFloat

lemma UnpackedFloat.CommonFormat.toFloatFormat_binary64 :
    toFloatFormat .binary64 = .binary64 := rfl

lemma UnpackedFloat.CommonFormat.toFloatFormat_binary32 :
    toFloatFormat .binary32 = .binary32 := rfl

lemma UnpackedFloat.CommonFormat.toFormat_binary64 :
    toFloatFormat .binary64 = .binary64 := rfl

lemma UnpackedFloat.CommonFormat.toFormat_binary32 :
    toFloatFormat .binary32 = .binary32 := rfl

noncomputable def RealFloat.ofFloat (f : Float) : RealFloat .binary64 :=
  ofUnbounded (UnpackedFloat.toUnboundedFloat (fmt := .binary64) f.toModel.unpack)

noncomputable def RealFloat.ofFloat32 (f : Float32) : RealFloat .binary32 :=
  ofUnbounded (UnpackedFloat.toUnboundedFloat (fmt := .binary32) f.toModel.unpack)

noncomputable def RealFloat.ofFloatModel (f : Float.Model) : RealFloat .binary64 :=
  ofUnbounded (UnpackedFloat.toUnboundedFloat (fmt := .binary64) f.unpack)

noncomputable def RealFloat.ofFloat32Model (f : Float32.Model) : RealFloat .binary32 :=
  ofUnbounded (UnpackedFloat.toUnboundedFloat (fmt := .binary32) f.unpack)

noncomputable def RealFloat.toFloat (f : RealFloat .binary64) : Float :=
  .ofModel <| .pack (UnpackedFloat.ofUnboundedFloat (fmt := .binary64) f.toUnbounded)

noncomputable def RealFloat.toFloat32 (f : RealFloat .binary32) : Float32 :=
  .ofModel <| .pack (UnpackedFloat.ofUnboundedFloat (fmt := .binary32) f.toUnbounded)

@[simp] lemma UnpackedFloat.two_le_exponentBits_binary32 : 2 ≤ UnpackedFloat.CommonFormat.binary32.toFormat.exponentBits := by decide
@[simp] lemma UnpackedFloat.two_le_exponentBits_binary64 : 2 ≤ UnpackedFloat.CommonFormat.binary64.toFormat.exponentBits := by decide

@[simp]
lemma RealFloat.toFloat_ofFloat (f : Float) :
    (ofFloat f).toFloat = f := by
  rw [← Float.toBits_inj, ← UInt64.toBitVec_inj]
  simp [Float.toBits, toFloat, Float.Model.pack, ofFloat,
    Float.Model.unpack, Float.Model.UnpackedFloat.pack_unpack_of_valid f.toModel.valid]

@[simp]
lemma RealFloat.toFloat32_ofFloat32 (f : Float32) :
    (ofFloat32 f).toFloat32 = f := by
  rw [← Float32.toBits_inj, ← UInt32.toBitVec_inj]
  simp [Float32.toBits, toFloat32, Float32.Model.pack, ofFloat32,
    Float32.Model.unpack, Float.Model.UnpackedFloat.pack_unpack_of_valid f.toModel.valid]

@[simp]
lemma RealFloat.ofFloat_toFloat (f : RealFloat .binary64) :
    ofFloat f.toFloat = f := by
  simp [ofFloat, toFloat, Float.Model.pack, Float.Model.unpack, UnpackedFloat.unpack_pack]

@[simp]
lemma RealFloat.ofFloat32_toFloat32 (f : RealFloat .binary32) :
    ofFloat32 f.toFloat32 = f := by
  simp [ofFloat32, toFloat32, Float32.Model.pack, Float32.Model.unpack]

@[simp]
lemma RealFloat.ofFloat_inj {f f' : Float} : ofFloat f = ofFloat f' ↔ f = f' := by
  grind [RealFloat.toFloat_ofFloat]

@[simp]
lemma RealFloat.ofFloat32_inj {f f' : Float32} : ofFloat32 f = ofFloat32 f' ↔ f = f' := by
  grind [RealFloat.toFloat32_ofFloat32]

@[simp]
lemma RealFloat.toFloat_inj {f f' : RealFloat .binary64} : toFloat f = toFloat f' ↔ f = f' := by
  grind [RealFloat.ofFloat_toFloat]

@[simp]
lemma RealFloat.toFloat32_inj {f f' : RealFloat .binary32} : toFloat32 f = toFloat32 f' ↔ f = f' := by
  grind [RealFloat.ofFloat32_toFloat32]

@[simp]
lemma RealFloat.ofFloat_add (a b : Float) :
    ofFloat (a + b) = (ofFloat a).add (ofFloat b) := by
  simp [Float.add, ofFloat, Float.Model.unpack, · + ·, Add.add,
    Float.Model.add, Float.Model.pack, UnpackedFloat.isRounded_add,
    UnpackedFloat.toUnboundedFloat_add, RealFloat.add]

@[simp]
lemma RealFloat.ofFloat32_add (a b : Float32) :
    ofFloat32 (a + b) = (ofFloat32 a).add (ofFloat32 b) := by
  simp [Float32.add, ofFloat32, Float32.Model.unpack, · + ·, Add.add,
    Float32.Model.add, Float32.Model.pack, UnpackedFloat.isRounded_add,
    UnpackedFloat.toUnboundedFloat_add, RealFloat.add]

@[simp]
lemma RealFloat.toFloat_add (a b : RealFloat .binary64) :
    (a.add b).toFloat = a.toFloat + b.toFloat := by simp [← ofFloat_inj]

@[simp]
lemma RealFloat.toFloat32_add (a b : RealFloat .binary32) :
    (a.add b).toFloat32 = a.toFloat32 + b.toFloat32 := by simp [← ofFloat32_inj]

@[simp]
lemma RealFloat.ofFloat_neg (a : Float) :
    ofFloat (-a) = -(ofFloat a) := by
  change ofFloat (Float.ofModel a.toModel.neg) = _
  simp [ofFloat, Float.Model.unpack, Float.Model.neg, Float.Model.pack, neg_ofUnbounded]

@[simp]
lemma RealFloat.ofFloat32_neg (a : Float32) :
    ofFloat32 (-a) = -(ofFloat32 a) := by
  change ofFloat32 (Float32.ofModel a.toModel.neg) = _
  simp [ofFloat32, Float32.Model.unpack, Float32.Model.neg, Float32.Model.pack, neg_ofUnbounded]

@[simp]
lemma RealFloat.toFloat_neg (a : RealFloat .binary64) :
    (-a).toFloat = -a.toFloat := by simp [← ofFloat_inj]

@[simp]
lemma RealFloat.toFloat32_neg (a : RealFloat .binary32) :
    (-a).toFloat32 = -a.toFloat32 := by simp [← ofFloat32_inj]

@[simp]
lemma RealFloat.ofFloat_abs (a : Float) :
    ofFloat a.abs = (ofFloat a).abs := by
  simp [ofFloat, Float.Model.unpack, Float.abs, Float.Model.abs, Float.Model.pack, ← ofUnbounded_abs]

@[simp]
lemma RealFloat.ofFloat32_abs (a : Float32) :
    ofFloat32 a.abs = (ofFloat32 a).abs := by
  simp [ofFloat32, Float32.Model.unpack, Float32.abs, Float32.Model.abs, Float32.Model.pack, ← ofUnbounded_abs]

@[simp]
lemma RealFloat.toFloat_abs (a : RealFloat .binary64) :
    a.abs.toFloat = a.toFloat.abs := by simp [← ofFloat_inj]

@[simp]
lemma RealFloat.toFloat32_abs (a : RealFloat .binary32) :
    a.abs.toFloat32 = a.toFloat32.abs := by simp [← ofFloat32_inj]

@[simp]
lemma RealFloat.ofFloat_sub (a b : Float) :
    ofFloat (a - b) = (ofFloat a).sub (ofFloat b) := by
  simp (config := { maxDischargeDepth := 3 }) [Float.sub, ofFloat,
    Float.Model.unpack, · - ·, Sub.sub, Float.Model.sub, Float.Model.pack,
    UnpackedFloat.isRounded_add, UnpackedFloat.toUnboundedFloat_add, RealFloat.add]

@[simp]
lemma RealFloat.ofFloat32_sub (a b : Float32) :
    ofFloat32 (a - b) = (ofFloat32 a).sub (ofFloat32 b) := by
  simp (config := { maxDischargeDepth := 3 }) [Float32.sub, ofFloat32,
    Float32.Model.unpack, · - ·, Sub.sub, Float32.Model.sub, Float32.Model.pack,
    UnpackedFloat.isRounded_add, UnpackedFloat.toUnboundedFloat_add, RealFloat.add]

@[simp]
lemma RealFloat.ofFloat_mul (a b : Float) :
    ofFloat (a * b) = (ofFloat a).mul (ofFloat b) := by
  simp [Float.mul, ofFloat, Float.Model.unpack, · * ·, Mul.mul,
    Float.Model.mul, Float.Model.pack, UnpackedFloat.isRounded_mul,
    UnpackedFloat.toUnboundedFloat_mul, RealFloat.mul]

@[simp]
lemma RealFloat.ofFloat32_mul (a b : Float32) :
    ofFloat32 (a * b) = (ofFloat32 a).mul (ofFloat32 b) := by
  simp [Float32.mul, ofFloat32, Float32.Model.unpack, · * ·, Mul.mul,
    Float32.Model.mul, Float32.Model.pack, UnpackedFloat.isRounded_mul,
    UnpackedFloat.toUnboundedFloat_mul, RealFloat.mul]

@[simp]
lemma RealFloat.toFloat_mul (a b : RealFloat .binary64) :
    (a.mul b).toFloat = a.toFloat * b.toFloat := by simp [← ofFloat_inj]

@[simp]
lemma RealFloat.toFloat32_mul (a b : RealFloat .binary32) :
    (a.mul b).toFloat32 = a.toFloat32 * b.toFloat32 := by simp [← ofFloat32_inj]

@[simp]
lemma RealFloat.ofFloat_div (a b : Float) :
    ofFloat (a / b) = (ofFloat a).div (ofFloat b) := by
  simp [Float.div, ofFloat, Float.Model.unpack, · / ·, Div.div,
    Float.Model.div, Float.Model.pack, UnpackedFloat.isRounded_div,
    UnpackedFloat.toUnboundedFloat_div, RealFloat.div]

@[simp]
lemma RealFloat.ofFloat32_div (a b : Float32) :
    ofFloat32 (a / b) = (ofFloat32 a).div (ofFloat32 b) := by
  simp [Float32.div, ofFloat32, Float32.Model.unpack, · / ·, Div.div,
    Float32.Model.div, Float32.Model.pack, UnpackedFloat.isRounded_div,
    UnpackedFloat.toUnboundedFloat_div, RealFloat.div]

@[simp]
lemma RealFloat.toFloat_div (a b : RealFloat .binary64) :
    (a.div b).toFloat = a.toFloat / b.toFloat := by simp [← ofFloat_inj]

@[simp]
lemma RealFloat.toFloat32_div (a b : RealFloat .binary32) :
    (a.div b).toFloat32 = a.toFloat32 / b.toFloat32 := by simp [← ofFloat32_inj]

@[simp]
lemma RealFloat.ofFloat_sqrt (a : Float) :
    ofFloat a.sqrt = (ofFloat a).sqrt := by
  simp [Float.sqrt, ofFloat, Float.Model.unpack,
    Float.Model.sqrt, Float.Model.pack, UnpackedFloat.isRounded_sqrt,
    UnpackedFloat.toUnboundedFloat_sqrt, RealFloat.sqrt]

@[simp]
lemma RealFloat.ofFloat32_sqrt (a : Float32) :
    ofFloat32 a.sqrt = (ofFloat32 a).sqrt := by
  simp [Float32.sqrt, ofFloat32, Float32.Model.unpack,
    Float32.Model.sqrt, Float32.Model.pack, UnpackedFloat.isRounded_sqrt,
    UnpackedFloat.toUnboundedFloat_sqrt, RealFloat.sqrt]

@[simp]
lemma RealFloat.toFloat_sqrt (a : RealFloat .binary64) :
    a.sqrt.toFloat = a.toFloat.sqrt := by simp [← ofFloat_inj]

@[simp]
lemma RealFloat.toFloat32_sqrt (a : RealFloat .binary32) :
    a.sqrt.toFloat32 = a.toFloat32.sqrt := by simp [← ofFloat32_inj]

lemma RealFloat.ofFloat_le {a b : Float} : ofFloat a ≤ ofFloat b ↔ a ≤ b := by
  change ofFloat a ≤ ofFloat b ↔ decide (a.toModel.le b.toModel) = true
  simp [Float.Model.le, ofFloat, ofUnbounded_eq_ofUnboundedInRange,
    Float.Model.unpack, UnpackedFloat.le_eq_toUnboundedFloat_le (fmt := .binary64)]

lemma RealFloat.ofFloat32_le {a b : Float32} : ofFloat32 a ≤ ofFloat32 b ↔ a ≤ b := by
  change ofFloat32 a ≤ ofFloat32 b ↔ decide (a.toModel.le b.toModel) = true
  simp [Float32.Model.le, ofFloat32, ofUnbounded_eq_ofUnboundedInRange,
    Float32.Model.unpack, UnpackedFloat.le_eq_toUnboundedFloat_le (fmt := .binary32)]

lemma RealFloat.toFloat_le {a b : RealFloat .binary64} : a.toFloat ≤ b.toFloat ↔ a ≤ b := by
  simp [← ofFloat_le]

lemma RealFloat.toFloat32_le {a b : RealFloat .binary32} : a.toFloat32 ≤ b.toFloat32 ↔ a ≤ b := by
  simp [← ofFloat32_le]

lemma RealFloat.ofFloat_lt {a b : Float} : ofFloat a < ofFloat b ↔ a < b := by
  change ofFloat a < ofFloat b ↔ decide (a.toModel.lt b.toModel) = true
  simp [Float.Model.lt, ofFloat, ofUnbounded_eq_ofUnboundedInRange,
    Float.Model.unpack, UnpackedFloat.lt_eq_toUnboundedFloat_lt (fmt := .binary64)]

lemma RealFloat.ofFloat32_lt {a b : Float32} : ofFloat32 a < ofFloat32 b ↔ a < b := by
  change ofFloat32 a < ofFloat32 b ↔ decide (a.toModel.lt b.toModel) = true
  simp [Float32.Model.lt, ofFloat32, ofUnbounded_eq_ofUnboundedInRange,
    Float32.Model.unpack, UnpackedFloat.lt_eq_toUnboundedFloat_lt (fmt := .binary32)]

lemma RealFloat.toFloat_lt {a b : RealFloat .binary64} : a.toFloat < b.toFloat ↔ a < b := by
  simp [← ofFloat_lt]

lemma RealFloat.toFloat32_lt {a b : RealFloat .binary32} : a.toFloat32 < b.toFloat32 ↔ a < b := by
  simp [← ofFloat32_lt]

lemma RealFloat.ofFloat_beq {a b : Float} : (ofFloat a == ofFloat b) = (a == b) := by
  change (ofFloat a == ofFloat b) = (a.toModel.beq b.toModel)
  simp [Float.Model.beq, ofFloat, ofUnbounded_eq_ofUnboundedInRange,
    Float.Model.unpack, UnpackedFloat.beq_eq_toUnboundedFloat_equiv (fmt := .binary64)]

lemma RealFloat.ofFloat32_beq {a b : Float32} : (ofFloat32 a == ofFloat32 b) = (a == b) := by
  change (ofFloat32 a == ofFloat32 b) = (a.toModel.beq b.toModel)
  simp [Float32.Model.beq, ofFloat32, ofUnbounded_eq_ofUnboundedInRange,
    Float32.Model.unpack, UnpackedFloat.beq_eq_toUnboundedFloat_equiv (fmt := .binary32)]

lemma RealFloat.toFloat_beq {a b : RealFloat .binary64} : (a.toFloat == b.toFloat) = (a == b) := by
  simp [← ofFloat_beq]

lemma RealFloat.toFloat32_beq {a b : RealFloat .binary32} : (a.toFloat32 == b.toFloat32) = (a == b) := by
  simp [← ofFloat32_beq]

lemma RealFloat.floatToUInt8_eq (a : Float) :
    a.toUInt8 = UInt8.ofNatClamp ⌊(ofFloat a).toReal⌋₊ := by
  simp [Float.toUInt8, ofFloat, Float.Model.unpack, Float.Model.toUInt8,
    UnpackedFloat.toUInt8_eq (fmt := .binary64)]

lemma RealFloat.float32ToUInt8_eq (a : Float32) :
    a.toUInt8 = UInt8.ofNatClamp ⌊(ofFloat32 a).toReal⌋₊ := by
  simp [Float32.toUInt8, ofFloat32, Float32.Model.unpack, Float32.Model.toUInt8,
    UnpackedFloat.toUInt8_eq (fmt := .binary32)]

lemma RealFloat.floatToUInt16_eq (a : Float) :
    a.toUInt16 = UInt16.ofNatClamp ⌊(ofFloat a).toReal⌋₊ := by
  simp [Float.toUInt16, ofFloat, Float.Model.unpack, Float.Model.toUInt16,
    UnpackedFloat.toUInt16_eq (fmt := .binary64)]

lemma RealFloat.float32ToUInt16_eq (a : Float32) :
    a.toUInt16 = UInt16.ofNatClamp ⌊(ofFloat32 a).toReal⌋₊ := by
  simp [Float32.toUInt16, ofFloat32, Float32.Model.unpack, Float32.Model.toUInt16,
    UnpackedFloat.toUInt16_eq (fmt := .binary32)]

lemma RealFloat.floatToUInt32_eq (a : Float) :
    a.toUInt32 = UInt32.ofNatClamp ⌊(ofFloat a).toReal⌋₊ := by
  simp [Float.toUInt32, ofFloat, Float.Model.unpack, Float.Model.toUInt32,
    UnpackedFloat.toUInt32_eq (fmt := .binary64)]

lemma RealFloat.float32ToUInt32_eq (a : Float32) :
    a.toUInt32 = UInt32.ofNatClamp ⌊(ofFloat32 a).toReal⌋₊ := by
  simp [Float32.toUInt32, ofFloat32, Float32.Model.unpack, Float32.Model.toUInt32,
    UnpackedFloat.toUInt32_eq (fmt := .binary32)]

lemma RealFloat.floatToUInt64_eq (a : Float) :
    a.toUInt64 = UInt64.ofNatClamp ⌊(ofFloat a).toReal⌋₊ := by
  simp [Float.toUInt64, ofFloat, Float.Model.unpack, Float.Model.toUInt64,
    UnpackedFloat.toUInt64_eq (fmt := .binary64)]

lemma RealFloat.float32ToUInt64_eq (a : Float32) :
    a.toUInt64 = UInt64.ofNatClamp ⌊(ofFloat32 a).toReal⌋₊ := by
  simp [Float32.toUInt64, ofFloat32, Float32.Model.unpack, Float32.Model.toUInt64,
    UnpackedFloat.toUInt64_eq (fmt := .binary32)]

lemma RealFloat.floatToUSize_eq (a : Float) :
    a.toUSize = USize.ofNatClamp ⌊(ofFloat a).toReal⌋₊ := by
  simp [Float.toUSize, ofFloat, Float.Model.unpack, Float.Model.toUSize,
    UnpackedFloat.toUSize_eq (fmt := .binary64)]

lemma RealFloat.float32ToUSize_eq (a : Float32) :
    a.toUSize = USize.ofNatClamp ⌊(ofFloat32 a).toReal⌋₊ := by
  simp [Float32.toUSize, ofFloat32, Float32.Model.unpack, Float32.Model.toUSize,
    UnpackedFloat.toUSize_eq (fmt := .binary32)]

-- These are opaque?

/-
lemma RealFloat.floatToInt8_eq (a : Float) :
    a.toInt8 = Int8.ofIntClamp (RoundingFunction.towardsZero (ofFloatModel a).toReal) := by
  simp [Float.toInt8, ofFloat, Float.Model.unpack, Float.Model.toInt8,
    UnpackedFloat.toInt8_eq (fmt := .binary64)]

lemma RealFloat.float32ToInt8_eq (a : Float32) :
    a.toInt8 = Int8.ofIntClamp (RoundingFunction.towardsZero (ofFloat32 a).toReal) := by
  simp [Float32.toInt8, ofFloat32, Float32.Model.unpack, Float32.Model.toInt8,
    UnpackedFloat.toInt8_eq (fmt := .binary32)]

lemma RealFloat.floatToInt16_eq (a : Float) :
    a.toInt16 = Int16.ofIntClamp (RoundingFunction.towardsZero (ofFloat a).toReal) := by
  simp [Float.toInt16, ofFloat, Float.Model.unpack, Float.Model.toInt16,
    UnpackedFloat.toInt16_eq (fmt := .binary64)]

lemma RealFloat.float32ToInt16_eq (a : Float32) :
    a.toInt16 = Int16.ofIntClamp (RoundingFunction.towardsZero (ofFloat32 a).toReal) := by
  simp [Float32.toInt16, ofFloat32, Float32.Model.unpack, Float32.Model.toInt16,
    UnpackedFloat.toInt16_eq (fmt := .binary32)]

lemma RealFloat.floatToInt32_eq (a : Float) :
    a.toInt32 = Int32.ofIntClamp (RoundingFunction.towardsZero (ofFloat a).toReal) := by
  simp [Float.toInt32, ofFloat, Float.Model.unpack, Float.Model.toInt32,
    UnpackedFloat.toInt32_eq (fmt := .binary64)]

lemma RealFloat.float32ToInt32_eq (a : Float32) :
    a.toInt32 = Int32.ofIntClamp (RoundingFunction.towardsZero (ofFloat32 a).toReal) := by
  simp [Float32.toInt32, ofFloat32, Float32.Model.unpack, Float32.Model.toInt32,
    UnpackedFloat.toInt32_eq (fmt := .binary32)]

lemma RealFloat.floatToInt64_eq (a : Float) :
    a.toInt64 = Int64.ofIntClamp (RoundingFunction.towardsZero (ofFloat a).toReal) := by
  simp [Float.toInt64, ofFloat, Float.Model.unpack, Float.Model.toInt64,
    UnpackedFloat.toInt64_eq (fmt := .binary64)]

lemma RealFloat.float32ToInt64_eq (a : Float32) :
    a.toInt64 = Int64.ofIntClamp (RoundingFunction.towardsZero (ofFloat32 a).toReal) := by
  simp [Float32.toInt64, ofFloat32, Float32.Model.unpack, Float32.Model.toInt64,
    UnpackedFloat.toInt64_eq (fmt := .binary32)]

lemma RealFloat.floatToISize_eq (a : Float) :
    a.toISize = ISize.ofIntClamp (RoundingFunction.towardsZero (ofFloat a).toReal) := by
  simp [Float.toISize, ofFloat, Float.Model.unpack, Float.Model.toISize,
    UnpackedFloat.toISize_eq (fmt := .binary64)]

lemma RealFloat.float32ToISize_eq (a : Float32) :
    a.toISize = ISize.ofIntClamp (RoundingFunction.towardsZero (ofFloat32 a).toReal) := by
  simp [Float32.toISize, ofFloat32, Float32.Model.unpack, Float32.Model.toISize,
    UnpackedFloat.toISize_eq (fmt := .binary32)]
-/

lemma RealFloat.floatToInt8_eq (a : Float.Model) :
    a.toInt8 = Int8.ofIntClamp (RoundingFunction.towardsZero (ofFloatModel a).toReal) := by
  simp [ofFloatModel, Float.Model.unpack, Float.Model.toInt8,
    UnpackedFloat.toInt8_eq (fmt := .binary64)]

lemma RealFloat.float32ToInt8_eq (a : Float32.Model) :
    a.toInt8 = Int8.ofIntClamp (RoundingFunction.towardsZero (ofFloat32Model a).toReal) := by
  simp [ofFloat32Model, Float32.Model.unpack, Float32.Model.toInt8,
    UnpackedFloat.toInt8_eq (fmt := .binary32)]

lemma RealFloat.floatToInt16_eq (a : Float.Model) :
    a.toInt16 = Int16.ofIntClamp (RoundingFunction.towardsZero (ofFloatModel a).toReal) := by
  simp [ofFloatModel, Float.Model.unpack, Float.Model.toInt16,
    UnpackedFloat.toInt16_eq (fmt := .binary64)]

lemma RealFloat.float32ToInt16_eq (a : Float32.Model) :
    a.toInt16 = Int16.ofIntClamp (RoundingFunction.towardsZero (ofFloat32Model a).toReal) := by
  simp [ofFloat32Model, Float32.Model.unpack, Float32.Model.toInt16,
    UnpackedFloat.toInt16_eq (fmt := .binary32)]

lemma RealFloat.floatToInt32_eq (a : Float.Model) :
    a.toInt32 = Int32.ofIntClamp (RoundingFunction.towardsZero (ofFloatModel a).toReal) := by
  simp [ofFloatModel, Float.Model.unpack, Float.Model.toInt32,
    UnpackedFloat.toInt32_eq (fmt := .binary64)]

lemma RealFloat.float32ToInt32_eq (a : Float32.Model) :
    a.toInt32 = Int32.ofIntClamp (RoundingFunction.towardsZero (ofFloat32Model a).toReal) := by
  simp [ofFloat32Model, Float32.Model.unpack, Float32.Model.toInt32,
    UnpackedFloat.toInt32_eq (fmt := .binary32)]

lemma RealFloat.floatToInt64_eq (a : Float.Model) :
    a.toInt64 = Int64.ofIntClamp (RoundingFunction.towardsZero (ofFloatModel a).toReal) := by
  simp [ofFloatModel, Float.Model.unpack, Float.Model.toInt64,
    UnpackedFloat.toInt64_eq (fmt := .binary64)]

lemma RealFloat.float32ToInt64_eq (a : Float32.Model) :
    a.toInt64 = Int64.ofIntClamp (RoundingFunction.towardsZero (ofFloat32Model a).toReal) := by
  simp [ofFloat32Model, Float32.Model.unpack, Float32.Model.toInt64,
    UnpackedFloat.toInt64_eq (fmt := .binary32)]

lemma RealFloat.floatToISize_eq (a : Float.Model) :
    a.toISize = ISize.ofIntClamp (RoundingFunction.towardsZero (ofFloatModel a).toReal) := by
  simp [ofFloatModel, Float.Model.unpack, Float.Model.toISize,
    UnpackedFloat.toISize_eq (fmt := .binary64)]

lemma RealFloat.float32ToISize_eq (a : Float32.Model) :
    a.toISize = ISize.ofIntClamp (RoundingFunction.towardsZero (ofFloat32Model a).toReal) := by
  simp [ofFloat32Model, Float32.Model.unpack, Float32.Model.toISize,
    UnpackedFloat.toISize_eq (fmt := .binary32)]

end LeanFloats
