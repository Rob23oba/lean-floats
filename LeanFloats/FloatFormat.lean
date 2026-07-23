module
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Tactic.Rify
public import LeanFloats.SimpleSign
public import LeanFloats.RoundingFunction

@[expose] public section

namespace LeanFloats

structure Base where
  value : Nat
  two_le_value : 2 ≤ value

attribute [coe] Base.value
attribute [grind! .] Base.two_le_value

instance : CoeOut Base ℕ where
  coe x := x.value

instance {b : Base} : b.value.AtLeastTwo := ⟨b.two_le_value⟩

@[simp] lemma Base.value_ne_zero (b : Base) : b.value ≠ 0 := by grind
@[simp] lemma Base.value_pos (b : Base) : 0 < b.value := by grind
@[simp] lemma Base.one_lt_value (b : Base) : 1 < b.value := by grind
@[simp] lemma Base.one_le_value (b : Base) : 1 ≤ b.value := by grind
@[simp] lemma Base.base_zpow_pos (b : Base) (i : ℤ) : 0 < (b : ℝ) ^ i := by simp [zpow_pos]
@[simp] lemma Base.base_zpow_ne_zero (b : Base) (i : ℤ) : (b : ℝ) ^ i ≠ 0 := by simp [zpow_ne_zero]
@[simp] lemma Base.base_zpow_nonneg (b : Base) (i : ℤ) : 0 ≤ (b : ℝ) ^ i := by simp [zpow_nonneg]
@[simp] lemma Base.not_base_zpow_nonpos (b : Base) (i : ℤ) : ¬ (b : ℝ) ^ i ≤ 0 := by simp

open Mathlib.Meta.Positivity Qq in
@[positivity Base.value _]
meta def Base.valuePositivityExt : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Nat), ~q(Base.value $x) => do
    assertInstancesCommute
    return .positive q(Base.value_pos $x)
  | _ => pure .none

instance {n : Nat} [h : n.AtLeastTwo] : OfNat Base n where
  ofNat := ⟨n, h.prop⟩

@[simp] lemma Base.value_ofNat (n : ℕ) [n.AtLeastTwo] : Base.value ofNat(n) = n := rfl

structure FloatFormat (base : Base) where
  infExp : Nat
  precision : Nat
  precision_pos : 0 < precision := by decide
  precision_lt_infExp : precision < infExp := by decide

namespace FloatFormat

abbrev binary32 : FloatFormat 2 where
  infExp := 128
  precision := 24

abbrev binary64 : FloatFormat 2 where
  infExp := 1024
  precision := 53

variable {base : Base} {f : FloatFormat base}

attribute [simp, grind! .] precision_lt_infExp precision_pos

@[grind =]
def minExp (f : FloatFormat base) : Int :=
  3 - f.infExp - f.precision

@[simp] lemma precision_ne_zero : f.precision ≠ 0 := by grind
@[simp] lemma one_lt_infExp : 1 < f.infExp := by grind
@[simp] lemma infExp_pos : 0 < f.infExp := by grind
@[simp] lemma infExp_ne_zero : f.infExp ≠ 0 := by grind
@[simp] lemma minExp_nonpos : f.minExp ≤ 0 := by grind

@[mk_iff]
inductive IsRounded (f : FloatFormat base) (x : ℝ) : Prop where
  | intro (exp : ℤ) (mant : ℤ) (hexp : f.minExp ≤ exp) (hmant : mant.natAbs < base ^ f.precision)
      (hx : x = mant * base ^ exp) : f.IsRounded x

@[mk_iff]
structure InRange (f : FloatFormat base) (x : ℝ) : Prop where
  abs_lt : |x| < base ^ f.infExp

noncomputable instance : Decidable (InRange f x) :=
  decidable_of_decidable_of_iff (inRange_iff f x).symm

@[mk_iff]
structure IsValidFloat (f : FloatFormat base) (x : ℝ) where
  isRounded : f.IsRounded x
  inRange : f.InRange x

lemma IsRounded.intro_le {exp : ℤ} {mant : ℤ}
    (hexp : f.minExp ≤ exp) (hmant : mant.natAbs ≤ base ^ f.precision) :
    f.IsRounded (mant * base ^ exp) := by
  by_cases hlt : mant.natAbs < base ^ f.precision
  · use exp, mant, hexp, hlt
  · have : mant = base ^ f.precision ∨ mant = -base ^ f.precision := by lia
    obtain rfl | rfl := this
    · use f.precision + exp, 1, by grind, by simp
      simp [zpow_add₀]
    · use f.precision + exp, -1, by grind, by simp
      simp [zpow_add₀]

lemma IsValidFloat.intro_lt {exp : ℤ} {mant : ℤ}
    (hexp_ge : f.minExp ≤ exp) (hexp_le : exp ≤ f.infExp - f.precision)
    (hmant : mant.natAbs < base ^ f.precision) :
    f.IsValidFloat (mant * base ^ exp) := by
  constructor
  · exact .intro_le hexp_ge hmant.le
  · constructor
    simp only [abs_mul, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast, abs_zpow, Nat.abs_cast]
    grw [hmant, hexp_le] <;> simp [← zpow_add₀, ← zpow_natCast]

lemma isRounded_natCast {n : ℕ} (h : n ≤ base ^ f.precision) : f.IsRounded n := by
  suffices f.IsRounded ((n : ℤ) * base ^ (0 : ℤ)) by simpa
  exact .intro_le f.minExp_nonpos h

lemma isValidFloat_natCast {n : ℕ} (h : n ≤ base ^ f.precision) : f.IsValidFloat n := by
  constructor
  · exact isRounded_natCast h
  · constructor
    grw [Nat.abs_cast, h, Nat.cast_pow, f.precision_lt_infExp]
    simp

@[simp]
lemma isRounded_base_zpow_iff {n : ℤ} : f.IsRounded (base ^ n) ↔ f.minExp ≤ n := by
  constructor
  · intro ⟨e, m, he, hm, heq⟩
    rw [← div_eq_iff (by simp), ← zpow_sub₀ (by simp)] at heq
    have : 0 < (m : ℝ) := by simp [← heq]
    replace : 1 ≤ (m : ℝ) := by norm_cast at this; norm_cast
    simp [← heq] at this
    lia
  · intro h
    exact .intro n 1 h (by simp) (by simp)

@[simp]
lemma isRounded_base_pow {n : ℕ} : f.IsRounded (base ^ n) := by
  rw [← zpow_natCast, isRounded_base_zpow_iff]
  grind

@[simp]
lemma inRange_base_zpow_iff {n : ℤ} : f.InRange (base ^ n) ↔ n < f.infExp := by
  simp [inRange_iff, ← zpow_natCast]

@[simp]
lemma inRange_base_pow_iff {n : ℕ} : f.InRange (base ^ n) ↔ n < f.infExp := by
  simp [inRange_iff, ← zpow_natCast]

@[simp]
lemma isValidFloat_base_zpow_iff {n : ℤ} : f.IsValidFloat (base ^ n) ↔ f.minExp ≤ n ∧ n < f.infExp := by
  simp [isValidFloat_iff]

@[simp]
lemma isValidFloat_base_pow_iff {n : ℕ} : f.IsValidFloat (base ^ n) ↔ n < f.infExp := by
  simp [isValidFloat_iff]

lemma IsRounded.neg {x : ℝ} (h : f.IsRounded x) :
    f.IsRounded (-x) := by
  obtain ⟨e, i, he, hi, rfl⟩ := h
  use e, -i, he
  · simp [hi]
  · simp

lemma InRange.neg {x : ℝ} (h : f.InRange x) :
    f.InRange (-x) := by simp_all [inRange_iff]

lemma IsValidFloat.neg {x : ℝ} (h : f.IsValidFloat x) :
    f.IsValidFloat (-x) := ⟨h.1.neg, h.2.neg⟩

lemma IsRounded.abs {x : ℝ} (h : f.IsRounded x) : f.IsRounded |x| := by
  grind [IsRounded.neg]

lemma InRange.abs {x : ℝ} (h : f.InRange x) :
    f.InRange |x| := by simp_all [inRange_iff]

lemma IsValidFloat.abs {x : ℝ} (h : f.IsValidFloat x) :
    f.IsValidFloat |x| := ⟨h.1.abs, h.2.abs⟩

lemma IsRounded.simpleSign_mul {x : ℝ} (h : f.IsRounded x) (s : SimpleSign) :
    f.IsRounded (s * x) := by
  cases s <;> simp [h, h.neg]

lemma IsRange.simpleSign_mul {x : ℝ} (h : f.InRange x) (s : SimpleSign) :
    f.InRange (s * x) := by
  cases s <;> simp [h, h.neg]

lemma IsValidFloat.simpleSign_mul {x : ℝ} (h : f.IsValidFloat x) (s : SimpleSign) :
    f.IsValidFloat (s * x) := by
  cases s <;> simp [h, h.neg]

@[simp]
lemma isRounded_neg_iff {x : ℝ} :
    f.IsRounded (-x) ↔ f.IsRounded x :=
  ⟨fun h => by simpa using h.neg, .neg⟩

@[simp]
lemma isRounded_abs_iff {x : ℝ} :
    f.IsRounded |x| ↔ f.IsRounded x := by
  grind [isRounded_neg_iff]

@[simp]
lemma isRounded_simpleSign_mul_iff {s : SimpleSign} {x : ℝ} :
    f.IsRounded (s * x) ↔ f.IsRounded x := by cases s <;> simp

@[simp]
lemma inRange_neg_iff {x : ℝ} :
    f.InRange (-x) ↔ f.InRange x :=
  ⟨fun h => by simpa using h.neg, .neg⟩

@[simp]
lemma inRange_abs_iff {x : ℝ} :
    f.InRange |x| ↔ f.InRange x := by
  grind [inRange_neg_iff]

@[simp]
lemma inRange_simpleSign_mul_iff {s : SimpleSign} {x : ℝ} :
    f.InRange (s * x) ↔ f.InRange x := by cases s <;> simp

@[simp]
lemma isValidFloat_neg_iff {x : ℝ} :
    f.IsValidFloat (-x) ↔ f.IsValidFloat x :=
  ⟨fun h => by simpa using h.neg, .neg⟩

@[simp]
lemma isValidFloat_abs_iff {x : ℝ} :
    f.IsValidFloat |x| ↔ f.IsValidFloat x := by
  simp [isValidFloat_iff]

@[simp]
lemma isValidFloat_simpleSign_mul_iff {s : SimpleSign} {x : ℝ} :
    f.IsValidFloat (s * x) ↔ f.IsValidFloat x := by
  simp [isValidFloat_iff]

@[simp]
lemma isRounded_zero : IsRounded f 0 :=
  .intro 0 0 f.minExp_nonpos (by simp) (by simp)

@[simp]
lemma inRange_zero : InRange f 0 := by
  simp [inRange_iff]

@[simp]
lemma isValidFloat_zero : IsValidFloat f 0 :=
  ⟨f.isRounded_zero, f.inRange_zero⟩

@[simp]
lemma isRounded_one : IsRounded f 1 := by
  use 0, 1, f.minExp_nonpos, by simp, by simp

@[simp]
lemma inRange_one : InRange f 1 := by
  rw [inRange_iff]
  norm_cast
  simp

@[simp]
lemma isValidFloat_one : IsValidFloat f 1 :=
  ⟨f.isRounded_one, f.inRange_one⟩

lemma pos_of_le_of_inRange_of_not_inRange {x y : ℝ}
    (hxy : x ≤ y) (hx : f.InRange x) (hy : ¬ f.InRange y) :
    0 < y := by
  simp only [inRange_iff, not_lt] at hx hy
  grind

lemma lt_zero_of_le_of_not_inRange_of_inRange {x y : ℝ}
    (hxy : x ≤ y) (hx : ¬ f.InRange x) (hy : f.InRange y) :
    x < 0 := by
  simp only [inRange_iff, not_lt] at hx hy
  grind

variable (f) in
noncomputable def getExponent (x : ℝ) : ℤ :=
  if x = 0 then
    f.minExp
  else
    max (Int.log base |x| + 1 - f.precision) f.minExp

@[simp]
lemma minExp_le_getExponent {x : ℝ} : f.minExp ≤ f.getExponent x := by
  grind [getExponent]

lemma getExponent_eq_minExp_iff {x : ℝ} :
    f.getExponent x = f.minExp ↔ |x| < base ^ (f.minExp + f.precision) := by
  simp +contextual [getExponent, Int.add_one_le_iff, ← Int.lt_zpow_iff_log_lt, or_iff_not_imp_left]

@[simp]
lemma getExponent_neg {x : ℝ} : f.getExponent (-x) = f.getExponent x := by
  grind [getExponent]

@[simp]
lemma getExponent_abs {x : ℝ} : f.getExponent |x| = f.getExponent x := by
  grind [getExponent]

@[simp]
lemma getExponent_simpleSign_mul {s : SimpleSign} {x : ℝ} :
    f.getExponent (s * x) = f.getExponent x := by
  cases s <;> simp

lemma lt_getExponent_of_ge {x : ℝ} {e : ℤ} (h : base ^ (e + f.precision) ≤ |x|) :
    e < f.getExponent x := by
  rw [getExponent]
  split
  · simp only [abs_zero, ← not_lt, Nat.cast_pos,
      Base.value_pos, zpow_pos, not_true_eq_false, *] at h
  · have : e + f.precision ≤ Int.log base |x| := by simp [← Int.zpow_le_iff_le_log, *]
    grw [← this, add_sub_right_comm, add_sub_cancel_right, ← le_max_left, Int.lt_add_one_iff]

lemma getExponent_le_of_lt {x : ℝ} {e : ℤ} (hx : |x| < base ^ (e + f.precision))
    (he : f.minExp ≤ e) : f.getExponent x ≤ e := by
  rw [getExponent]
  split
  · exact he
  · have : Int.log base |x| < e + f.precision := by simp [← Int.lt_zpow_iff_log_lt, *]
    grw [Int.add_one_le_of_lt this, add_sub_right_comm, sub_add_cancel]
    simp [he]

lemma getExponent_le_iff {x : ℝ} {e : ℤ} :
    f.getExponent x ≤ e ↔ |x| < base ^ (e + f.precision) ∧ f.minExp ≤ e := by
  constructor
  · intro h
    constructor
    · contrapose! h
      exact lt_getExponent_of_ge h
    · grw [minExp_le_getExponent, h]
  · intro ⟨h₁, h₂⟩
    exact getExponent_le_of_lt h₁ h₂

lemma getExponent_le_iff_of_le {x : ℝ} {e : ℤ} (h : f.minExp ≤ e) :
    f.getExponent x ≤ e ↔ |x| < base ^ (e + f.precision) := by
  simp [getExponent_le_iff, h]

lemma lt_getExponent_iff_of_le {x : ℝ} {e : ℤ} (h : f.minExp ≤ e) :
    e < f.getExponent x ↔ base ^ (e + f.precision) ≤ |x| := by
  contrapose!; exact getExponent_le_iff_of_le h

lemma abs_lt_zpow_getExponent {x : ℝ} : |x| < base ^ (f.getExponent x + f.precision) := by
  simpa using mt (f.lt_getExponent_of_ge (x := x) (e := f.getExponent x))

@[gcongr]
lemma getExponent_mono_of_nonneg {x y : ℝ} (hxy : x ≤ y) (hx : 0 ≤ x) :
    f.getExponent x ≤ f.getExponent y := by
  grw [getExponent_le_iff_of_le minExp_le_getExponent, hxy, ← getExponent_le_iff_of_le minExp_le_getExponent]

@[gcongr low]
lemma getExponent_anti_of_nonpos {x y : ℝ} (hxy : x ≤ y) (hx : y ≤ 0) :
    f.getExponent y ≤ f.getExponent x := by
  grw [getExponent_le_iff_of_le minExp_le_getExponent, ← hxy, ← getExponent_le_iff_of_le minExp_le_getExponent]

lemma exists_nat_of_getExponent_lt_getExponent {a b : ℝ}
    (hexp : f.getExponent a < f.getExponent b) (hb : 0 ≤ b) :
    ∃ n : ℕ, a ≤ n * base ^ f.getExponent b ∧ n * base ^ f.getExponent b ≤ b := by
  let diff : ℕ := (f.getExponent b - f.getExponent a - 1).toNat
  have hexpb : f.getExponent b = f.getExponent a + diff + 1 := by lia
  use base ^ (f.precision - 1)
  have hexp' : f.getExponent a + diff < f.getExponent b := by lia
  have hmin : f.minExp ≤ f.getExponent a := minExp_le_getExponent
  rw [lt_getExponent_iff_of_le (by lia), abs_of_nonneg hb] at hexp'
  suffices a ≤ base ^ (f.getExponent a + diff + f.precision) by
    simpa [hexpb, ← zpow_natCast, ← zpow_add₀, add_comm (f.precision : ℤ), hexp']
  apply le_of_abs_le
  grw [f.abs_lt_zpow_getExponent]
  exact zpow_le_zpow_right₀ (by simp) (by lia)

variable (f) in
noncomputable def getMantissa (x : ℝ) : ℤ :=
  ⌊x / base ^ f.getExponent x⌋

lemma IsRounded.getMantissa_mul_base_pow_getExponent {x : ℝ} (h : IsRounded f x) :
    f.getMantissa x * base ^ f.getExponent x = x := by
  obtain ⟨e, i, he, hi, rfl⟩ := h
  have : f.getExponent (↑i * base ^ e) ≤ e := by
    apply getExponent_le_of_lt
    · simp only [abs_mul, abs_zpow, Nat.abs_cast, add_comm e, ne_eq, Nat.cast_eq_zero,
        Base.value_ne_zero, not_false_eq_true, zpow_add₀, zpow_natCast]
      gcongr; grw [← Int.cast_abs, Int.abs_eq_natAbs]
      norm_cast
    · assumption
  rw [← sub_nonneg] at this
  rw [getMantissa, mul_div_assoc, ← zpow_sub₀ (by simp),
    ← Int.toNat_of_nonneg this]
  norm_cast
  rw [Int.floor_intCast]
  simp [Nat.cast_pow, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    ← zpow_natCast, Int.toNat_of_nonneg this, zpow_sub₀]
  field

lemma IsRounded.abs_getMantissa_mul_base_pow_getExponent {x : ℝ} (h : IsRounded f x) :
    |(f.getMantissa x : ℝ)| * base ^ f.getExponent x = |x| := by
  simpa using congrArg (|·|) h.getMantissa_mul_base_pow_getExponent

lemma IsRounded.natAbs_getMantissa_lt {x : ℝ} (h : IsRounded f x) :
    (f.getMantissa x).natAbs < base ^ f.precision := by
  rify
  have := h.getMantissa_mul_base_pow_getExponent
  rw [← eq_div_iff (by simp)] at this
  simp [this, abs_div, div_lt_iff₀, ← zpow_natCast, ← zpow_add₀,
    abs_lt_zpow_getExponent, add_comm _ (f.getExponent _)]

lemma InRange.getExponent_le {x : ℝ} (h : InRange f x) :
    f.getExponent x ≤ f.infExp - f.precision := by
  apply getExponent_le_of_lt
  · simp [h.abs_lt]
  · grind

lemma isRounded_round {round : RoundingFunction} (x : ℝ) :
    f.IsRounded (round (x / base ^ f.getExponent x) * base ^ f.getExponent x) := by
  refine .intro_le f.minExp_le_getExponent ?_
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs, abs_le]
  have := f.abs_lt_zpow_getExponent (x := x)
  rw [zpow_add₀ (by simp), ← div_lt_iff₀' (by simp),
    ← abs_of_nonneg (a := (base ^ f.getExponent x : ℝ)) (by simp), ← abs_div, abs_lt] at this
  grw [← this.1, this.2]
  norm_cast
  rw [RoundingFunction.apply_intCast, RoundingFunction.apply_natCast]
  simp

lemma round_mono {round : RoundingFunction} {x y : ℝ} (h : x ≤ y) :
    (round (x / base ^ f.getExponent x) * base ^ f.getExponent x : ℝ) ≤
      round (y / base ^ f.getExponent y) * base ^ f.getExponent y := by
  wlog hy : 0 ≤ y
  · specialize @this base f round.opposite (-y) (-x) (neg_le_neg h) (by grind)
    simpa [neg_div] using this
  by_cases hx : x ≤ 0
  · trans 0
    · simp [mul_nonpos_iff, round.apply_nonpos, div_nonpos_iff, hx]
    · positivity
  · replace hx := le_of_not_ge hx
    have hexp : f.getExponent x ≤ f.getExponent y := by grw [h]
    rcases hexp.lt_or_eq with hexp | hexp
    · obtain ⟨n, h₁, h₂⟩ := f.exists_nat_of_getExponent_lt_getExponent hexp hy
      grw [h₁, mul_div_assoc, ← zpow_sub₀ (by simp), ← pow_toNat_eq_zpow (by lia), ← h₂]
      norm_cast
      rw [round.apply_natCast]
      simp [hexp.le, pow_toNat_eq_zpow, zpow_sub₀, ← mul_div_assoc]
    · simp only [hexp, Nat.cast_pos, Base.value_pos, zpow_pos, mul_le_mul_iff_left₀, ge_iff_le]
      grw [h]

lemma round_eq_self {round : RoundingFunction} {x : ℝ} (h : f.IsRounded x) :
    (round (x / base ^ f.getExponent x) * base ^ f.getExponent x : ℝ) = x := by
  nth_rw 1 [← h.getMantissa_mul_base_pow_getExponent]
  simpa using h.getMantissa_mul_base_pow_getExponent

lemma isRounded_mul_base_pow_of_getExponent {m : ℕ} {e : ℤ} (h : f.getExponent (m * base ^ e) ≤ e) :
    f.IsRounded (m * base ^ e) := by
  obtain ⟨h₁, h₂⟩ := getExponent_le_iff.mp h
  simp only [mul_comm _ (base ^ e : ℝ), abs_mul, abs_zpow, Nat.abs_cast, ne_eq, Nat.cast_eq_zero,
    Base.value_ne_zero, not_false_eq_true, zpow_add₀, zpow_natCast, Nat.cast_pos, Base.value_pos,
    zpow_pos, mul_lt_mul_iff_right₀] at h₁
  norm_cast at h₁
  use e, m, h₂, by simpa using h₁
  rfl

lemma getMantissa_mul_base_pow {m : ℕ} {e : ℤ} (h : f.getExponent (m * base ^ e) = e) :
    f.getMantissa (m * base ^ e) = m := by
  rify; simpa [h] using (isRounded_mul_base_pow_of_getExponent h.le).getMantissa_mul_base_pow_getExponent

@[simp]
lemma IsRounded.getMantissa_eq_zero_iff {x : ℝ} (h : IsRounded f x) :
    f.getMantissa x = 0 ↔ x = 0 := by
  conv_rhs => rw [← h.getMantissa_mul_base_pow_getExponent]
  simp

@[simp]
lemma IsRounded.getMantissa_nonneg_iff {x : ℝ} (h : IsRounded f x) :
    0 ≤ f.getMantissa x ↔ 0 ≤ x := by
  conv_rhs => rw [← h.getMantissa_mul_base_pow_getExponent]
  simp

@[simp]
lemma IsRounded.getMantissa_nonpos_iff {x : ℝ} (h : IsRounded f x) :
    f.getMantissa x ≤ 0 ↔ x ≤ 0 := by
  conv_rhs => rw [← h.getMantissa_mul_base_pow_getExponent]
  simp [mul_nonpos_iff]

@[simp]
lemma IsRounded.getMantissa_lt_zero_iff {x : ℝ} (h : IsRounded f x) :
    f.getMantissa x < 0 ↔ x < 0 := by contrapose!; rw [h.getMantissa_nonneg_iff]

@[simp]
lemma IsRounded.getMantissa_pos_iff {x : ℝ} (h : IsRounded f x) :
    0 < f.getMantissa x ↔ 0 < x := by contrapose!; rw [h.getMantissa_nonpos_iff]

@[simp]
lemma IsRounded.getMantissa_neg {x : ℝ} (h : IsRounded f x) :
    f.getMantissa (-x) = -f.getMantissa x := by
  have h₁ := h.getMantissa_mul_base_pow_getExponent
  have h₂ := h.neg.getMantissa_mul_base_pow_getExponent
  conv_rhs at h₂ => rw [← h₁]
  simpa [← neg_mul, ← Int.cast_neg] using h₂

@[simp]
lemma IsRounded.getMantissa_abs {x : ℝ} (h : IsRounded f x) :
    f.getMantissa |x| = |f.getMantissa x| := by
  cases abs_cases x <;> simp [*, abs_of_nonneg, abs_of_neg]

lemma IsRounded.compare_eq_of_nonneg {x y : ℝ}
    (hx : IsRounded f x) (hy : IsRounded f y) (hx' : 0 ≤ x) (hy' : 0 ≤ y) :
    compare x y = (compare (f.getExponent x) (f.getExponent y)).then
      (compare (f.getMantissa x) (f.getMantissa y)) := by
  obtain he | he | he := lt_trichotomy (f.getExponent x) (f.getExponent y)
  · rw [Std.compare_eq_lt.mpr he, Ordering.lt_then, Std.compare_eq_lt]
    contrapose! he
    grw [he]
  · replace hx := hx.getMantissa_mul_base_pow_getExponent
    replace hy := hy.getMantissa_mul_base_pow_getExponent
    rw [he] at hx
    rw [he, Std.compare_self, Ordering.eq_then]
    conv => enter [1, 1]; rw [← hx]
    conv => enter [1, 2]; rw [← hy]
    simp
  · rw [Std.compare_eq_gt.mpr he, Ordering.gt_then, Std.compare_eq_gt]
    contrapose! he
    grw [he]

lemma IsRounded.compare_eq_of_nonpos {x y : ℝ}
    (hx : IsRounded f x) (hy : IsRounded f y) (hx' : x ≤ 0) (hy' : y ≤ 0) :
    compare x y = (compare (f.getExponent y) (f.getExponent x)).then
      (compare (f.getMantissa x) (f.getMantissa y)) := by
  rw [← compare_neg, compare_eq_of_nonneg hy.neg hx.neg (by simpa) (by simpa),
    getExponent_neg, getExponent_neg, hx.getMantissa_neg, hy.getMantissa_neg, compare_neg]

noncomputable def maxValue (f : FloatFormat base) : ℝ :=
  (base ^ f.precision - 1) * base ^ (f.infExp - f.precision : ℤ)

lemma isRounded_maxValue : IsRounded f f.maxValue := by
  use f.infExp - f.precision, base ^ f.precision - 1, by grind, by grind
  simp [maxValue]

@[simp]
lemma maxValue_nonneg : 0 ≤ f.maxValue := by
  simp [maxValue, ← zpow_natCast]

@[simp]
lemma abs_maxValue : |f.maxValue| = f.maxValue := abs_of_nonneg maxValue_nonneg

lemma inRange_maxValue : InRange f f.maxValue := by
  rw [inRange_iff, abs_maxValue]
  simp [sub_mul, ← zpow_add₀, ← zpow_natCast, maxValue]

lemma isValidFloat_maxValue : IsValidFloat f f.maxValue :=
  ⟨f.isRounded_maxValue, f.inRange_maxValue⟩

lemma abs_le_maxValue_of_isValidFloat {x : ℝ} (h : f.IsValidFloat x) : |x| ≤ f.maxValue := by
  rw [← h.isRounded.getMantissa_mul_base_pow_getExponent]
  simp only [abs_mul, abs_zpow, Nat.abs_cast]
  rw [← Int.cast_abs, Int.abs_eq_natAbs, maxValue]
  grw [h.inRange.getExponent_le, Nat.le_sub_one_of_lt h.isRounded.natAbs_getMantissa_lt] <;> simp

lemma le_maxValue_of_isValidFloat {x : ℝ} (h : f.IsValidFloat x) : x ≤ f.maxValue :=
  le_of_abs_le (abs_le_maxValue_of_isValidFloat h)

lemma neg_maxValue_le_of_isValidFloat {x : ℝ} (h : f.IsValidFloat x) : -f.maxValue ≤ x :=
  neg_le_of_abs_le (abs_le_maxValue_of_isValidFloat h)

end FloatFormat

end LeanFloats
