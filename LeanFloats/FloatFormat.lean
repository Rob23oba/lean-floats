module
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Tactic.Rify
public import LeanFloats.SimpleSign

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

lemma abs_lt_zpow_getExponent {x : ℝ} : |x| < base ^ (f.getExponent x + f.precision) := by
  simpa using mt (f.lt_getExponent_of_ge (x := x) (e := f.getExponent x))

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

lemma IsRounded.getMantissa_eq_zero_iff {x : ℝ} (h : IsRounded f x) :
    f.getMantissa x = 0 ↔ x = 0 := by
  constructor
  · intro h'
    rw [← h.getMantissa_mul_base_pow_getExponent, h']
    simp
  · rintro rfl
    simp [getMantissa]

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
  rw [inRange_iff, abs_of_nonneg maxValue_nonneg]
  simp [sub_mul, ← zpow_add₀, ← zpow_natCast, maxValue]

lemma isValidFloat_maxValue : IsValidFloat f f.maxValue :=
  ⟨f.isRounded_maxValue, f.inRange_maxValue⟩

lemma abs_le_maxValue_of_isValidFloat {x : ℝ} (h : f.IsValidFloat x) :
    |x| ≤ f.maxValue := by
  rw [← h.isRounded.getMantissa_mul_base_pow_getExponent]
  simp only [abs_mul, abs_zpow, Nat.abs_cast]
  rw [← Int.cast_abs, Int.abs_eq_natAbs, maxValue]
  grw [h.inRange.getExponent_le, Nat.le_sub_one_of_lt h.isRounded.natAbs_getMantissa_lt] <;> simp

end FloatFormat

end LeanFloats
