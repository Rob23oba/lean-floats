module
public import LeanFloats.RealFloats.Basic
public import LeanFloats.UnboundedFloat.Rounding
public import LeanFloats.RoundingFunction
public import Mathlib.Analysis.Real.Sqrt

@[expose] public noncomputable section

namespace LeanFloats.RealFloat

variable {base : Base} {fmt : FloatFormat base}

def maxFinite (s : SimpleSign) : RealFloat fmt :=
  .ofValidNNReal s (NNReal.mk fmt.maxValue fmt.maxValue_nonneg) (by exact fmt.isValidFloat_maxValue)

def overflowValue (s : SimpleSign) (round : RoundingFunction) : RealFloat fmt :=
  if round.RepelsAtInfinity s then
    .maxFinite s
  else
    .infinity s

def ofUnbounded (x : UnboundedFloat fmt)
    (round : RoundingFunction := .tiesToEven) : RealFloat fmt :=
  if h : fmt.InRange x.toFiniteReal then
    ofUnboundedInRange x h
  else
    overflowValue (.ofValue x.sign) round

def roundReal (x : ℝ) (zeroSign : SimpleSign := 1)
    (round : RoundingFunction := .tiesToEven) : RealFloat fmt :=
  ofUnbounded (.roundReal x zeroSign round) round

def roundNNReal (s : SimpleSign) (x : NNReal)
    (round : RoundingFunction := .tiesToEven) : RealFloat fmt :=
  roundReal (s * x) s round

lemma roundNNReal_eq_roundReal (s x round) :
    (roundNNReal s x round : RealFloat fmt) = roundReal (s * x) s round := (rfl)

variable {round : RoundingFunction}

@[simp]
lemma isFinite_maxFinite (s) : (maxFinite s : RealFloat fmt) ≠ nan := by simp [maxFinite]

@[simp]
lemma overflowValue_ne_nan (s round) : (overflowValue s round : RealFloat fmt) ≠ nan := by
  rw [overflowValue]
  split <;> simp

@[simp]
lemma sign_maxFinite (s) : (maxFinite s : RealFloat fmt).sign = s := by simp [maxFinite]

@[simp]
lemma sign_overflowValue (s round) : (overflowValue s round : RealFloat fmt).sign = s := by
  rw [overflowValue]
  split <;> simp

@[simp]
lemma maxFinite_inj {s s'} : (maxFinite s : RealFloat fmt) = maxFinite s' ↔ s = s' := by simp [maxFinite]

@[simp]
lemma overflowValue_inj {s s'} {round} :
    (overflowValue s round : RealFloat fmt) = overflowValue s' round ↔ s = s' := by
  grind [sign_overflowValue]

@[simp]
lemma neg_maxFinite {s} : -(maxFinite s : RealFloat fmt) = maxFinite (-s) := by
  simp [maxFinite]

@[simp]
lemma neg_overflowValue {s round} :
    -(overflowValue s round : RealFloat fmt) = overflowValue (-s) round.opposite := by
  simp [overflowValue, apply_ite (-· : RealFloat fmt → _)]

@[simp]
lemma abs_maxFinite {s} : (maxFinite s : RealFloat fmt).abs = maxFinite 1 := by
  simp [maxFinite]

@[simp]
lemma abs_overflowValue {s} {round : RoundingFunction} [round.NegStable] :
    (overflowValue s round : RealFloat fmt).abs = overflowValue 1 round := by
  simp [overflowValue, apply_ite RealFloat.abs,
    RoundingFunction.repelsAtInfinity_iff_repelsAtInfinity_one]

@[simp]
lemma ofUnbounded_nan : ofUnbounded (.nan : UnboundedFloat fmt) round = nan := by
  simp [ofUnbounded]

@[simp]
lemma ofUnbounded_infinity {s : SimpleSign} :
    ofUnbounded (.infinity s : UnboundedFloat fmt) round = infinity s := by
  simp [ofUnbounded]

lemma ofUnbounded_ofValidNNReal {s : SimpleSign} {x : NNReal} (h : fmt.IsRounded x) :
    ofUnbounded (.ofValidNNReal s x h) round =
      if h' : fmt.InRange x then ofValidNNReal s x ⟨h, h'⟩
      else overflowValue s round := by
  simp [ofUnbounded]

lemma ofUnbounded_ofValidReal {x : ℝ} (h : fmt.IsRounded x) (zs : SimpleSign) :
    ofUnbounded (.ofValidReal x h zs) round =
      if h' : fmt.InRange x then ofValidReal x ⟨h, h'⟩ zs
      else overflowValue (.ofValue x zs) round := by
  simp [ofUnbounded]

lemma ofUnbounded_ofValidEReal {x : EReal} (h : fmt.IsRounded x.toReal) {zs : SimpleSign} :
    ofUnbounded (.ofValidEReal x h zs) round =
      if h' : fmt.InRange x.toReal then ofValidEReal x ⟨h, h'⟩ zs
      else overflowValue (.ofValue x zs) round := by
  simp [ofUnbounded]

@[simp, norm_cast]
lemma ofUnbounded_toUnbounded (x : RealFloat fmt) : ofUnbounded x.toUnbounded round = x := by
  simp [ofUnbounded]

@[simp]
lemma toUnbounded_ofUnbounded {x : UnboundedFloat fmt} (h : fmt.InRange x.toFiniteReal) :
    (ofUnbounded x round).toUnbounded = x := by
  simp [ofUnbounded, h]

@[simp]
lemma ofUnbounded_roundReal (x : ℝ) (zs : SimpleSign) (round) :
    ofUnbounded (.roundReal x zs round : UnboundedFloat fmt) round = roundReal x zs round :=
  (rfl)

@[simp]
lemma ofUnbounded_roundNNReal (s : SimpleSign) (x : NNReal) (round) :
    ofUnbounded (.roundNNReal s x round : UnboundedFloat fmt) round = roundNNReal s x round :=
  (rfl)

lemma ofUnbounded_neg {x : UnboundedFloat fmt} : ofUnbounded (-x) round = -ofUnbounded x round.opposite := by
  simp only [ofUnbounded, UnboundedFloat.toFiniteReal_neg, FloatFormat.inRange_neg_iff,
    UnboundedFloat.sign_neg]
  split
  · simp
  · cases x <;> simp_all [← SimpleSign.coe_neg]

lemma neg_ofUnbounded {x : UnboundedFloat fmt} : -ofUnbounded x round = ofUnbounded (-x) round.opposite := by
  simp [ofUnbounded_neg]

lemma ofUnbounded_abs {x : UnboundedFloat fmt} [round.NegStable] :
    ofUnbounded x.abs round = (ofUnbounded x round).abs := by
  cases x <;> simp [ofUnbounded, SimpleSign.ofValue_of_nonneg, apply_dite RealFloat.abs]

@[simp]
lemma sign_ofUnbounded {x : UnboundedFloat fmt} {round} :
    (ofUnbounded x round).sign = x.sign := by
  rw [ofUnbounded]
  split
  · simp
  · cases x <;> simp_all

@[simp]
lemma ofUnbounded_eq_nan_iff {x : UnboundedFloat fmt} : ofUnbounded x round = nan ↔ x = .nan := by
  rw [ofUnbounded]
  split
  · simp
  · rename_i h
    contrapose h
    simp_all

@[simp]
lemma roundReal_ne_nan (x : ℝ) (zs round) :
    (roundReal x zs round : RealFloat fmt) ≠ nan := by
  simp [← ofUnbounded_roundReal]

@[simp]
lemma roundNNReal_ne_nan (s x round) :
    (roundNNReal s x round : RealFloat fmt) ≠ nan := by
  simp [roundNNReal_eq_roundReal]

@[simp]
lemma sign_roundReal (x zs round) :
    (roundReal x zs round : RealFloat fmt).sign = SimpleSign.ofValue x zs := by
  simp [← ofUnbounded_roundReal]

@[simp]
lemma sign_roundNNReal (s x round) :
    (roundNNReal s x round : RealFloat fmt).sign = s := by
  simp [roundNNReal_eq_roundReal, SimpleSign.ofValue_coe_mul_eq_self]

lemma roundReal_eq_roundReal_ofValue (x zs round) :
    (roundReal x zs round : RealFloat fmt) = roundReal x (.ofValue x zs) round := by
  simp [← ofUnbounded_roundReal, ← UnboundedFloat.roundReal_eq_roundReal_ofValue]

lemma roundReal_eq_roundNNReal (x zs round) :
    (roundReal x zs round : RealFloat fmt) = roundNNReal (.ofValue x zs) x.nnabs round := by
  simp [roundNNReal_eq_roundReal, ← roundReal_eq_roundReal_ofValue]

@[simp]
lemma neg_roundReal {x zs round} :
    -(roundReal x zs round : RealFloat fmt) = roundReal (-x) (-zs) round.opposite := by
  simp [← ofUnbounded_roundReal, neg_ofUnbounded]

@[simp]
lemma neg_roundNNReal {s x round} :
    -(roundNNReal s x round : RealFloat fmt) = roundNNReal (-s) x round.opposite := by
  simp [roundNNReal_eq_roundReal]

@[simp]
lemma abs_roundReal {x zs} {round : RoundingFunction} [round.NegStable] :
    (roundReal x zs round : RealFloat fmt).abs = roundReal |x| 1 round := by
  simp [← ofUnbounded_roundReal, ← ofUnbounded_abs]

@[simp]
lemma abs_roundNNReal {s x} {round : RoundingFunction} [round.NegStable] :
    (roundNNReal s x round : RealFloat fmt).abs = roundNNReal 1 x round := by
  simp [roundNNReal_eq_roundReal]

@[simp]
lemma roundNNReal_sign_inj {s s' x round} :
    (roundNNReal s x round : RealFloat fmt) = roundNNReal s' x round ↔ s = s' := by
  grind [sign_roundNNReal]

@[simp]
lemma roundReal_sign_inj {x zs zs' round} :
    (roundReal x zs round : RealFloat fmt) = roundReal x zs' round ↔ x = 0 → zs = zs' := by
  simp [roundReal_eq_roundNNReal]

lemma roundReal_eq_of_isRounded {x : ℝ} (h : fmt.IsRounded x) (zs : SimpleSign) :
    roundReal x zs round =
      if h' : fmt.InRange x then ofValidReal x ⟨h, h'⟩ zs
      else overflowValue (.ofValue x zs) round := by
  simp [← ofUnbounded_roundReal, UnboundedFloat.roundReal_eq_ofValidReal h, ofUnbounded_ofValidReal]

lemma roundReal_eq_ofValidReal {x : ℝ} (h : fmt.IsValidFloat x) (zs : SimpleSign) :
    roundReal x zs round = ofValidReal x h zs := by
  simp [roundReal_eq_of_isRounded h.isRounded, h.inRange]

lemma roundReal_eq_ofValidNNReal {x : NNReal} (h : fmt.IsValidFloat x) (s : SimpleSign) :
    roundReal (s * x) s round = ofValidNNReal s x h := by
  simp [roundReal_eq_ofValidReal (h.simpleSign_mul s), ofValidReal_def,
    SimpleSign.ofValue_coe_mul_eq_self]

lemma roundNNReal_eq_ofValidNNReal {x : NNReal} (h : fmt.IsValidFloat x) (s : SimpleSign) :
    roundNNReal s x round = ofValidNNReal s x h := by
  apply roundReal_eq_ofValidNNReal

lemma roundReal_eq_ofValidNNReal_pos {x : NNReal} (h : fmt.IsValidFloat x) :
    roundReal x 1 round = ofValidNNReal 1 x h := by
  simpa using roundReal_eq_ofValidNNReal h 1

lemma roundReal_eq_ofValidNNReal_neg {x : NNReal} (h : fmt.IsValidFloat x) :
    roundReal (-x) (-1) round = ofValidNNReal (-1) x h := by
  simpa using roundReal_eq_ofValidNNReal h (-1)

instance {n : Nat} : OfNat (RealFloat fmt) n where
  ofNat := roundReal n

lemma ofNat_eq_roundReal_tiesToEven (n : ℕ) : (ofNat(n) : RealFloat fmt) = roundReal n := (rfl)

lemma roundReal_natCast_eq_of_le {n : ℕ} (hle : (n : ℕ) ≤ base ^ fmt.precision) :
    (roundReal n : RealFloat fmt) = .ofValidNNReal 1 n (fmt.isValidFloat_natCast hle) := by
  rw [← NNReal.coe_natCast]
  apply roundReal_eq_ofValidNNReal_pos

lemma zero_eq_ofValidNNReal : (0 : RealFloat fmt) = .ofValidNNReal 1 0 (by exact fmt.isValidFloat_zero) := by
  rw [ofNat_eq_roundReal_tiesToEven, roundReal_natCast_eq_of_le (by simp)]
  simp

lemma one_eq_ofValidNNReal : (1 : RealFloat fmt) = .ofValidNNReal 1 1 (by exact fmt.isValidFloat_one) := by
  rw [ofNat_eq_roundReal_tiesToEven, roundReal_natCast_eq_of_le (by simp [one_le_pow_iff])]
  simp

lemma ofValidNNReal_neg_one_eq_neg_zero :
    .ofValidNNReal (-1) 0 (by exact fmt.isValidFloat_zero) = (-0 : RealFloat fmt) := by
  simp [zero_eq_ofValidNNReal]

@[simp]
lemma ofValidNNReal_eq_zero_iff {s x h} :
    (.ofValidNNReal s x h : RealFloat fmt) = 0 ↔ s = 1 ∧ x = 0 := by
  simp [zero_eq_ofValidNNReal]

@[simp]
lemma ofValidNNReal_eq_neg_zero_iff {s x h} :
    (.ofValidNNReal s x h : RealFloat fmt) = -0 ↔ s = -1 ∧ x = 0 := by
  simp [zero_eq_ofValidNNReal]

@[simp] lemma isFinite_zero : (0 : RealFloat fmt).IsFinite := by simp [zero_eq_ofValidNNReal]
@[simp] lemma isFinite_one : (1 : RealFloat fmt).IsFinite := by simp [one_eq_ofValidNNReal]

@[simp] lemma abs_ofNat {n} : (ofNat(n) : RealFloat fmt).abs = ofNat(n) := by simp [ofNat_eq_roundReal_tiesToEven]

@[simp] lemma toFiniteReal_zero : (0 : RealFloat fmt).toFiniteReal = 0 := by simp [zero_eq_ofValidNNReal]
@[simp] lemma toFiniteReal_one : (1 : RealFloat fmt).toFiniteReal = 1 := by simp [one_eq_ofValidNNReal]

@[simp] lemma toEReal_zero : (0 : RealFloat fmt).toEReal = 0 := by simp [zero_eq_ofValidNNReal]
@[simp] lemma toEReal_one : (1 : RealFloat fmt).toEReal = 1 := by simp [one_eq_ofValidNNReal]

@[simp] lemma toReal_zero : (0 : RealFloat fmt).toReal = 0 := by simp [zero_eq_ofValidNNReal]
@[simp] lemma toReal_one : (1 : RealFloat fmt).toReal = 1 := by simp [one_eq_ofValidNNReal]

@[simp] lemma ofUnbounded_zero : (ofUnbounded 0 round : RealFloat fmt) = 0 := by
  simp [UnboundedFloat.zero_eq_ofValidNNReal, ofUnbounded]

@[simp] lemma ofUnbounded_one : (ofUnbounded 1 round : RealFloat fmt) = 1 := by
  simp [UnboundedFloat.one_eq_ofValidNNReal, ofUnbounded, one_eq_ofValidNNReal]

@[simp, norm_cast]
lemma toUnbounded_zero : (0 : RealFloat fmt).toUnbounded = 0 := by
  simp [zero_eq_ofValidNNReal, UnboundedFloat.zero_eq_ofValidNNReal]

@[simp, norm_cast]
lemma toUnbounded_one : (1 : RealFloat fmt).toUnbounded = 1 := by
  simp [one_eq_ofValidNNReal, UnboundedFloat.one_eq_ofValidNNReal]

@[simp] lemma sign_ofNat {n : Nat} : (ofNat(n) : RealFloat fmt).sign = 1 := by
  simp [ofNat_eq_roundReal_tiesToEven, SimpleSign.ofValue_of_nonneg]

@[simp]
lemma neg_zero_equiv_zero : (-0 : RealFloat fmt) ≈ 0 := by
  rw [RealFloat.equiv_def]
  simp

@[simp]
lemma zero_equiv_neg_zero : (0 : RealFloat fmt) ≈ -0 := by
  rw [RealFloat.equiv_def]
  simp

lemma equiv_cases {a b : RealFloat fmt} :
    a ≈ b ↔ (a ≠ nan ∧ a = b) ∨ (a = 0 ∧ b = -0) ∨ (a = -0 ∧ b = 0) := by
  simp [← toUnbounded_equiv, UnboundedFloat.equiv_cases, ← toUnbounded_inj,
    -toUnbounded_eq_nan_iff]

lemma ext_toEReal_sign {a b : RealFloat fmt}
    (h₁ : a.toEReal = b.toEReal) (h₂ : a.sign = b.sign) : a = b := by
  rw [← toUnbounded_inj]
  apply UnboundedFloat.ext_toEReal_sign <;> simp_all

protected def add (a b : RealFloat fmt) (round : RoundingFunction := .tiesToEven) : RealFloat fmt :=
  ofUnbounded (a.toUnbounded.add b.toUnbounded round) round

lemma add_eq_ofUnbounded {x y : RealFloat fmt} :
    x.add y round = ofUnbounded (x.toUnbounded.add y.toUnbounded round) round := by
  simp [RealFloat.add]

@[simp] lemma nan_add (a : RealFloat fmt) (round : RoundingFunction) : nan.add a round = nan := by
  simp [add_eq_ofUnbounded]

@[simp] lemma add_nan (a : RealFloat fmt) (round : RoundingFunction) : a.add nan round = nan := by
  simp [add_eq_ofUnbounded]

@[simp] lemma infinity_add_self (s : SimpleSign) (round : RoundingFunction) :
    (infinity s : RealFloat fmt).add (infinity s) round = infinity s := by
  simp [add_eq_ofUnbounded]

@[simp] lemma infinity_add_neg (s : SimpleSign) (round : RoundingFunction) :
    (infinity s : RealFloat fmt).add (infinity (-s)) round = nan := by
  simp [add_eq_ofUnbounded]

@[simp] lemma infinity_neg_add (s : SimpleSign) (round : RoundingFunction) :
    (infinity (-s) : RealFloat fmt).add (infinity s) round = nan := by
  simp [add_eq_ofUnbounded]

lemma infinity_add_infinity (s s' : SimpleSign) (round : RoundingFunction) :
    (infinity s : RealFloat fmt).add (infinity s') round = if s = s' then infinity s else .nan := by
  simp [add_eq_ofUnbounded, UnboundedFloat.infinity_add_infinity, apply_ite (ofUnbounded · round)]

@[simp] lemma infinity_add_ofValidNNReal (s : SimpleSign) (s' x h) (round : RoundingFunction) :
    (infinity s : RealFloat fmt).add (ofValidNNReal s' x h) round = infinity s := by
  simp [add_eq_ofUnbounded]

@[simp] lemma ofValidNNReal_add_infinity (s x h) (s' : SimpleSign) (round : RoundingFunction) :
    (ofValidNNReal s x h : RealFloat fmt).add (infinity s') round = infinity s' := by
  simp [add_eq_ofUnbounded]

lemma IsFinite.infinity_add {f : RealFloat fmt} (h : IsFinite f) (s : SimpleSign) (round) :
    (infinity s).add f round = infinity s := by cases h; simp

lemma IsFinite.add_infinity {f : RealFloat fmt} (h : IsFinite f) (s : SimpleSign) (round) :
    f.add (infinity s : RealFloat fmt) round = infinity s := by cases h; simp

lemma ofValidNNReal_add_ofValidNNReal (s x h) (s' x' h') (round : RoundingFunction) :
    (ofValidNNReal s x h : RealFloat fmt).add (ofValidNNReal s' x' h') round =
      roundReal (s * x + s' * x') (max s s') round := (rfl)

@[simp]
lemma ofUnboundedInRange_add_ofUnboundedInRange {x y : UnboundedFloat fmt}
    (hx : fmt.InRange x.toFiniteReal) (hy : fmt.InRange y.toFiniteReal) :
    (ofUnboundedInRange x hx).add (ofUnboundedInRange y hy) round = ofUnbounded (x.add y round) round := by
  simp [add_eq_ofUnbounded]

protected lemma add_comm (a b : RealFloat fmt) (round : RoundingFunction) :
    a.add b round = b.add a round := by
  simp [add_eq_ofUnbounded, UnboundedFloat.add_comm]

@[simp]
protected lemma add_neg_zero (a : RealFloat fmt) (round : RoundingFunction) :
    a.add (-0) round = a := by
  simp [add_eq_ofUnbounded]

@[simp]
protected lemma neg_zero_add (a : RealFloat fmt) (round : RoundingFunction) :
    (-0 : RealFloat fmt).add a round = a := by
  simp [add_eq_ofUnbounded]

lemma add_zero_eq_ite {a : RealFloat fmt} {round : RoundingFunction} :
    a.add 0 round = if a = -0 then 0 else a := by
  simp [add_eq_ofUnbounded, UnboundedFloat.add_zero_eq_ite, ← toUnbounded_inj,
    apply_ite (ofUnbounded · round)]

@[simp]
lemma zero_add_zero {round : RoundingFunction} : (0 : RealFloat fmt).add 0 round = 0 := by
  simp [add_zero_eq_ite]

lemma zero_add_eq_ite {a : RealFloat fmt} {round : RoundingFunction} :
    (0 : RealFloat fmt).add a round = if a = -0 then 0 else a := by
  rw [RealFloat.add_comm, add_zero_eq_ite]

lemma add_zero_equiv {a : RealFloat fmt} {round : RoundingFunction}
    (h : a ≠ nan) : a.add 0 round ≈ a := by
  rw [add_zero_eq_ite]
  split <;> simp_all

lemma zero_add_equiv {a : RealFloat fmt} {round : RoundingFunction}
    (h : a ≠ nan) : (0 : RealFloat fmt).add a round ≈ a := by
  rw [RealFloat.add_comm]
  exact RealFloat.add_zero_equiv h

/-
@[gcongr]
protected lemma add_equiv {a b c d : RealFloat fmt} {round : RoundingFunction}
    (hab : a ≈ b) (hcd : c ≈ d) : a.add c round ≈ b.add d round := by
  rw [RealFloat.equiv_cases] at hab hcd
  obtain ⟨ha, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hab <;>
    obtain ⟨ha, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hcd <;>
    simp [*, add_zero_equiv, zero_add_equiv, equiv_comm (b := add _ _ _)]
-/

@[simp]
protected def sub (a b : RealFloat fmt) (round : RoundingFunction := .tiesToEven) : RealFloat fmt :=
  a.add (-b) round

protected def mul (a b : RealFloat fmt) (round : RoundingFunction := .tiesToEven) : RealFloat fmt :=
  ofUnbounded (a.toUnbounded.mul b.toUnbounded round) round

lemma mul_eq_ofUnbounded {x y : RealFloat fmt} :
    x.mul y round = ofUnbounded (x.toUnbounded.mul y.toUnbounded round) round := by
  simp [RealFloat.mul]

@[simp] lemma nan_mul {a : RealFloat fmt} : nan.mul a round = nan := by simp [mul_eq_ofUnbounded]
@[simp] lemma mul_nan {a : RealFloat fmt} : a.mul nan round = nan := by simp [mul_eq_ofUnbounded]
@[simp] lemma infinity_mul_infinity {s s' : SimpleSign} :
    (infinity s : RealFloat fmt).mul (infinity s') round = infinity (s * s') := by simp [mul_eq_ofUnbounded]

lemma infinity_mul_ofValidNNReal {s : SimpleSign} {s' x h} :
    (infinity s : RealFloat fmt).mul (ofValidNNReal s' x h) round =
      if x = 0 then nan else infinity (s * s') := by
  simp [mul_eq_ofUnbounded, UnboundedFloat.infinity_mul_ofValidNNReal, apply_ite (ofUnbounded · round)]

lemma ofValidNNReal_mul_infinity {s : SimpleSign} {s' x h} :
    (ofValidNNReal s' x h).mul (infinity s : RealFloat fmt) round =
      if x = 0 then nan else infinity (s' * s) := by
  simp [mul_eq_ofUnbounded, UnboundedFloat.ofValidNNReal_mul_infinity, apply_ite (ofUnbounded · round)]

lemma ofValidNNReal_mul_ofValidNNReal {s x h} {s' x' h'} :
    (ofValidNNReal s x h).mul (ofValidNNReal s' x' h' : RealFloat fmt) round =
      roundNNReal (s * s') (x * x') round := by
  simp [mul_eq_ofUnbounded, UnboundedFloat.ofValidNNReal_mul_ofValidNNReal]

@[simp]
lemma ofUnboundedInRange_mul_ofUnboundedInRange {x y : UnboundedFloat fmt}
    (hx : fmt.InRange x.toFiniteReal) (hy : fmt.InRange y.toFiniteReal) :
    (ofUnboundedInRange x hx).mul (ofUnboundedInRange y hy) round = ofUnbounded (x.mul y round) round := by
  simp [mul_eq_ofUnbounded]

protected lemma mul_comm (x y : RealFloat fmt) :
    x.mul y round = y.mul x round := by
  simp [mul_eq_ofUnbounded, UnboundedFloat.mul_comm]

@[simp]
protected lemma neg_mul (x y : RealFloat fmt) :
    (-x).mul y round = -x.mul y round.opposite := by
  simp [mul_eq_ofUnbounded, neg_ofUnbounded]

@[simp]
protected lemma mul_neg (x y : RealFloat fmt) :
    x.mul (-y) round = -x.mul y round.opposite := by
  simp [mul_eq_ofUnbounded, neg_ofUnbounded]

@[simp] protected lemma mul_one (x : RealFloat fmt) : x.mul 1 round = x := by simp [mul_eq_ofUnbounded]
@[simp] protected lemma one_mul (x : RealFloat fmt) : (1 : RealFloat fmt).mul x round = x := by simp [mul_eq_ofUnbounded]

@[simp] lemma infinity_mul_zero {s : SimpleSign} :
    (infinity s : RealFloat fmt).mul 0 round = nan := by simp [mul_eq_ofUnbounded]

@[simp] lemma zero_mul_infinity {s : SimpleSign} :
    (0 : RealFloat fmt).mul (infinity s) round = nan := by simp [mul_eq_ofUnbounded]

protected def div (a b : RealFloat fmt) (round : RoundingFunction := .tiesToEven) : RealFloat fmt :=
  ofUnbounded (a.toUnbounded.div b.toUnbounded round) round

lemma div_eq_ofUnbounded {x y : RealFloat fmt} :
    x.div y round = ofUnbounded (x.toUnbounded.div y.toUnbounded round) round := by
  simp [RealFloat.div]

@[simp] lemma nan_div {a : RealFloat fmt} : nan.div a round = nan := by simp [div_eq_ofUnbounded]
@[simp] lemma div_nan {a : RealFloat fmt} : a.div nan round = nan := by simp [div_eq_ofUnbounded]

@[simp] lemma infinity_div_infinity {s s' : SimpleSign} :
    (infinity s : RealFloat fmt).div (infinity s') round = nan := by simp [div_eq_ofUnbounded]
@[simp] lemma infinity_div_ofValidNNReal {s s' : SimpleSign} {x h} :
    (infinity s : RealFloat fmt).div (ofValidNNReal s' x h) round = infinity (s * s') := by simp [div_eq_ofUnbounded]

lemma ofValidNNReal_div_infinity {s s' : SimpleSign} {x h} :
    (ofValidNNReal s' x h).div (infinity s : RealFloat fmt) round = ofValidNNReal (s' * s) 0 (by simp) := by
  simp [div_eq_ofUnbounded, UnboundedFloat.ofValidNNReal_div_infinity, ofUnbounded]

@[simp]
lemma ofUnboundedInRange_div_ofUnboundedInRange {x y : UnboundedFloat fmt}
    (hx : fmt.InRange x.toFiniteReal) (hy : fmt.InRange y.toFiniteReal) :
    (ofUnboundedInRange x hx).div (ofUnboundedInRange y hy) round = ofUnbounded (x.div y round) round := by
  simp [div_eq_ofUnbounded]

@[simp]
lemma zero_div_zero : (0 : RealFloat fmt).div 0 round = nan := by
  simp [div_eq_ofUnbounded]

lemma ofValidNNReal_div_ofValidNNReal {s x h} {s' x' h'} :
    (ofValidNNReal s x h).div (ofValidNNReal s' x' h' : RealFloat fmt) round =
      if x' = 0 then
        if x = 0 then .nan else .infinity (s * s')
      else
        roundNNReal (s * s') (x / x') round := by
  simp [div_eq_ofUnbounded, UnboundedFloat.ofValidNNReal_div_ofValidNNReal, apply_ite (ofUnbounded · round)]

@[simp]
lemma div_one {x : RealFloat fmt} : (x : RealFloat fmt).div 1 round = x := by
  simp [div_eq_ofUnbounded]

@[simp]
lemma neg_div {x y : RealFloat fmt} : (-x : RealFloat fmt).div y round = -x.div y round.opposite := by
  simp [div_eq_ofUnbounded, neg_ofUnbounded]

@[simp]
lemma div_neg {x y : RealFloat fmt} : (x : RealFloat fmt).div (-y) round = -x.div y round.opposite := by
  simp [div_eq_ofUnbounded, neg_ofUnbounded]

protected def sqrt (a : RealFloat fmt) (round : RoundingFunction := .tiesToEven) : RealFloat fmt :=
  ofUnbounded (a.toUnbounded.sqrt round) round

lemma sqrt_eq_ofUnbounded {x : RealFloat fmt} :
    x.sqrt round = ofUnbounded (x.toUnbounded.sqrt round) round := by
  simp [RealFloat.sqrt]

@[simp] lemma sqrt_nan : (nan : RealFloat fmt).sqrt round = nan := by simp [sqrt_eq_ofUnbounded]
@[simp] lemma sqrt_infinity_one : (infinity 1 : RealFloat fmt).sqrt round = infinity 1 := by simp [sqrt_eq_ofUnbounded]
@[simp] lemma sqrt_infinity_neg_one : (infinity (-1) : RealFloat fmt).sqrt round = nan := by simp [sqrt_eq_ofUnbounded]

lemma sqrt_ofValidNNReal {s x h} :
    (ofValidNNReal s x h : RealFloat fmt).sqrt round =
      if (s * x : ℝ) < 0 then .nan else roundReal x.sqrt s round := by
  simp [sqrt_eq_ofUnbounded, UnboundedFloat.sqrt_ofValidNNReal, apply_ite (ofUnbounded · round)]

@[simp]
lemma sqrt_ofUnboundedInRange {x : UnboundedFloat fmt} (hx : fmt.InRange x.toFiniteReal) :
    (ofUnboundedInRange x hx).sqrt round = ofUnbounded (x.sqrt round) round := by
  simp [sqrt_eq_ofUnbounded]

lemma sqrt_ofValidNNReal_one {x h} :
    (ofValidNNReal 1 x h : RealFloat fmt).sqrt round = roundReal x.sqrt 1 round := by
  simp [sqrt_ofValidNNReal]

lemma sqrt_ofValidNNReal_neg_one {x h} :
    (ofValidNNReal (-1) x h : RealFloat fmt).sqrt round =
      if x = 0 then -0 else nan := by
  simp [sqrt_eq_ofUnbounded, UnboundedFloat.sqrt_ofValidNNReal_neg_one, apply_ite (ofUnbounded · round), ofUnbounded_neg]

@[simp]
lemma sqrt_zero : (0 : RealFloat fmt).sqrt = 0 := by
  simp [sqrt_eq_ofUnbounded]

@[simp]
lemma sqrt_neg_zero : (-0 : RealFloat fmt).sqrt = -0 := by
  simp [sqrt_eq_ofUnbounded, ofUnbounded_neg]

end LeanFloats.RealFloat
