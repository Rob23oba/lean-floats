module
public import LeanFloats.RealFloats.Basic
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

def roundReal (x : ℝ) (zeroSign : SimpleSign := 1)
    (round : RoundingFunction := .tiesToEven) : RealFloat fmt :=
  let e := fmt.getExponent x
  let x' : ℝ := round (x / base ^ e) * base ^ e
  if h : fmt.InRange x' then
    ofValidNNReal (.ofValue x zeroSign) x'.nnabs ⟨.abs ?_, h.abs⟩
  else
    overflowValue (.ofValue x zeroSign) round
where finally
  refine .intro_le fmt.minExp_le_getExponent ?_
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs, abs_le]
  have := fmt.abs_lt_zpow_getExponent (x := x)
  rw [zpow_add₀ (by simp), ← div_lt_iff₀' (by simp),
    ← abs_of_nonneg (a := (base ^ e : ℝ)) (by simp), ← abs_div, abs_lt] at this
  grw [← this.1, this.2]
  norm_cast
  rw [RoundingFunction.apply_intCast, RoundingFunction.apply_natCast]
  simp

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
lemma roundReal_ne_nan (x : ℝ) (zs round) :
    (roundReal x zs round : RealFloat fmt) ≠ nan := by
  rw [roundReal]
  split <;> simp

@[simp]
lemma roundNNReal_ne_nan (s x round) :
    (roundNNReal s x round : RealFloat fmt) ≠ nan := by simp [roundNNReal_eq_roundReal]

@[simp]
lemma sign_maxFinite (s) : (maxFinite s : RealFloat fmt).sign = s := by simp [maxFinite]

@[simp]
lemma sign_overflowValue (s round) : (overflowValue s round : RealFloat fmt).sign = s := by
  rw [overflowValue]
  split <;> simp

@[simp]
lemma sign_roundReal (x zs round) :
    (roundReal x zs round : RealFloat fmt).sign = SimpleSign.ofValue x zs := by
  rw [roundReal]
  split <;> simp

@[simp]
lemma sign_roundNNReal (s x round) :
    (roundNNReal s x round : RealFloat fmt).sign = s := by
  simp [roundNNReal_eq_roundReal, SimpleSign.ofValue_coe_mul_eq_self]

lemma roundReal_eq_roundReal_ofValue (x zs round) :
    (roundReal x zs round : RealFloat fmt) = roundReal x (.ofValue x zs) round := by
  simp [roundReal]

lemma roundReal_eq_roundNNReal (x zs round) :
    (roundReal x zs round : RealFloat fmt) = roundNNReal (.ofValue x zs) x.nnabs round := by
  simp [roundNNReal_eq_roundReal, ← roundReal_eq_roundReal_ofValue]

lemma roundReal_eq_of_isRounded {x : ℝ} (h : fmt.IsRounded x) (zs : SimpleSign) :
    roundReal x zs round =
      if h' : fmt.InRange x then ofValidReal x ⟨h, h'⟩ zs
      else overflowValue (.ofValue x zs) round := by
  unfold roundReal
  extract_lets e x'
  have : x' = x := by
    unfold x'
    rw [← h.getMantissa_mul_base_pow_getExponent]
    simp [e]
  simp [this, ofValidReal]

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

@[simp] lemma isFinite_zero : (0 : RealFloat fmt).IsFinite := by simp [zero_eq_ofValidNNReal]
@[simp] lemma isFinite_one : (1 : RealFloat fmt).IsFinite := by simp [one_eq_ofValidNNReal]

@[simp] lemma toEReal_zero : (0 : RealFloat fmt).toEReal = 0 := by simp [zero_eq_ofValidNNReal]
@[simp] lemma toEReal_one : (1 : RealFloat fmt).toEReal = 1 := by simp [one_eq_ofValidNNReal]

@[simp] lemma toReal_zero : (0 : RealFloat fmt).toReal = 0 := by simp [zero_eq_ofValidNNReal]
@[simp] lemma toReal_one : (1 : RealFloat fmt).toReal = 1 := by simp [one_eq_ofValidNNReal]

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
  constructor
  · intro h
    rw [RealFloat.equiv_def] at h
    obtain ⟨ha, hb, hab⟩ := h
    match a, b with
    | .infinity s, .infinity s' => cases s <;> cases s' <;> simp at hab <;> simp
    | .ofValidNNReal s _ _, .infinity s' => cases s <;> cases s' <;> simp at hab
    | .infinity s, .ofValidNNReal s' _ _ => rw [eq_comm] at hab; cases s <;> cases s' <;> simp at hab
    | .ofValidNNReal s x h, .ofValidNNReal s' x' h' =>
      simp only [toEReal_ofValidNNReal] at hab
      obtain rfl | rfl := s.eq_self_or_neg s'
      · simp only [SimpleSign.coe_mul_inj, EReal.coe_ennreal_eq_coe_ennreal_iff,
          ENNReal.coe_inj] at hab
        simp [hab]
      · cases s'
        · rw [eq_iff_eq_zero_of_nonpos_of_nonneg (by simp) (by simp)] at hab
          simp only [SimpleSign.coe_neg, SimpleSign.coe_one, neg_mul, one_mul,
            EReal.neg_eq_zero_iff, EReal.coe_ennreal_eq_zero, ENNReal.coe_eq_zero] at hab
          simp [hab, zero_eq_ofValidNNReal]
        · rw [eq_iff_eq_zero_of_nonneg_of_nonpos (by simp) (by simp)] at hab
          simp only [SimpleSign.coe_neg, SimpleSign.coe_one, neg_mul, one_mul,
            EReal.neg_eq_zero_iff, EReal.coe_ennreal_eq_zero, ENNReal.coe_eq_zero] at hab
          simp [hab, zero_eq_ofValidNNReal]
  · rintro (⟨ha, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [*]

lemma ext_toEReal_sign {a b : RealFloat fmt}
    (h₁ : a.toEReal = b.toEReal) (h₂ : a.sign = b.sign) : a = b := by
  by_cases ha : a = nan
  · simp_all [eq_comm (a := (0 : SignType))]
  by_cases hb : b = nan
  · simp_all
  have eqv : a ≈ b := by simp [RealFloat.equiv_def, *]
  rw [equiv_cases] at eqv
  obtain ⟨_, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := eqv <;> simp_all

def add (a b : RealFloat fmt) (round : RoundingFunction := .tiesToEven) : RealFloat fmt :=
  match a, b with
  | .nan, _ => .nan
  | _, .nan => .nan
  | .infinity s, .infinity s' =>
    if s = s' then a else .nan
  | .infinity _, _ => a
  | _, .infinity _ => b
  | .ofValidNNReal s x _, .ofValidNNReal s' x' _ =>
    roundReal (s * x + s' * x') (max s s') round

@[simp] lemma nan_add (a : RealFloat fmt) (round : RoundingFunction) : nan.add a round = nan := (rfl)

@[simp] lemma add_nan (a : RealFloat fmt) (round : RoundingFunction) : a.add nan round = nan := by cases a <;> rfl

@[simp] lemma infinity_add_self (s : SimpleSign) (round : RoundingFunction) :
    (infinity s : RealFloat fmt).add (infinity s) round = infinity s := by cases s <;> rfl

@[simp] lemma infinity_add_neg (s : SimpleSign) (round : RoundingFunction) :
    (infinity s : RealFloat fmt).add (infinity (-s)) round = nan := by cases s <;> rfl

@[simp] lemma infinity_neg_add (s : SimpleSign) (round : RoundingFunction) :
    (infinity (-s) : RealFloat fmt).add (infinity s) round = nan := by cases s <;> rfl

lemma infinity_add_infinity (s s' : SimpleSign) (round : RoundingFunction) :
    (infinity s : RealFloat fmt).add (infinity s') round = if s = s' then infinity s else .nan := (rfl)

@[simp] lemma infinity_add_ofValidNNReal (s : SimpleSign) (s' x h) (round : RoundingFunction) :
    (infinity s : RealFloat fmt).add (ofValidNNReal s' x h) round = infinity s := (rfl)

@[simp] lemma ofValidNNReal_add_infinity (s x h) (s' : SimpleSign) (round : RoundingFunction) :
    (ofValidNNReal s x h : RealFloat fmt).add (infinity s') round = infinity s' := (rfl)

lemma IsFinite.infinity_add {f : RealFloat fmt} (h : IsFinite f) (s : SimpleSign) (round) :
    (infinity s).add f round = infinity s := by cases h; simp

lemma IsFinite.add_infinity {f : RealFloat fmt} (h : IsFinite f) (s : SimpleSign) (round) :
    f.add (infinity s : RealFloat fmt) round = infinity s := by cases h; simp

lemma ofValidNNReal_add_ofValidNNReal (s x h) (s' x' h') (round : RoundingFunction) :
    (ofValidNNReal s x h : RealFloat fmt).add (ofValidNNReal s' x' h') round =
      roundReal (s * x + s' * x') (max s s') round := (rfl)

protected lemma add_comm (a b : RealFloat fmt) (round : RoundingFunction) :
    a.add b round = b.add a round := by
  cases a <;> cases b <;>
    simp +contextual [infinity_add_infinity, ofValidNNReal_add_ofValidNNReal,
      add_comm, max_comm, eq_comm]

@[simp]
protected lemma add_neg_zero (a : RealFloat fmt) (round : RoundingFunction) :
    a.add (-0) round = a := by
  rw [zero_eq_ofValidNNReal, neg_ofValidNNReal]
  cases a
  · rename_i s _ h
    cases s <;> simp [ofValidNNReal_add_ofValidNNReal, roundReal_eq_ofValidNNReal_pos h,
      roundReal_eq_ofValidNNReal_neg h]
  · simp
  · simp

@[simp]
protected lemma neg_zero_add (a : RealFloat fmt) (round : RoundingFunction) :
    (-0 : RealFloat fmt).add a round = a := by
  rw [RealFloat.add_comm, RealFloat.add_neg_zero]

lemma add_zero_eq_ite {a : RealFloat fmt} {round : RoundingFunction} :
    a.add 0 round = if a = -0 then 0 else a := by
  split
  · simp_all
  rename_i hne
  cases a
  · rename_i s h₁ h₂
    rw [zero_eq_ofValidNNReal] at hne ⊢
    rw [ofValidNNReal_add_ofValidNNReal]
    cases s
    · simp [roundReal_eq_ofValidNNReal_pos h₂]
    · simp only [neg_ofValidNNReal, ofValidNNReal.injEq, true_and] at hne
      rw [roundReal_eq_roundReal_ofValue]
      simp [SimpleSign.ofValue_of_neg, zero_le.lt_of_ne' hne,
        roundReal_eq_ofValidNNReal_neg h₂]
  · simp [zero_eq_ofValidNNReal]
  · simp

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
def sub (a b : RealFloat fmt) (round : RoundingFunction := .tiesToEven) : RealFloat fmt :=
  a.add (-b) round

def mul (a b : RealFloat fmt) (round : RoundingFunction := .tiesToEven) : RealFloat fmt :=
  match a, b with
  | .nan, _ => .nan
  | _, .nan => .nan
  | .infinity s, .infinity s' => .infinity (s * s')
  | .infinity s, .ofValidNNReal s' x _ =>
    if x = 0 then .nan else .infinity (s * s')
  | .ofValidNNReal s x _, .infinity s' =>
    if x = 0 then .nan else .infinity (s * s')
  | .ofValidNNReal s x _, .ofValidNNReal s' x' _ =>
    roundNNReal (s * s') (x * x') round

def div (a b : RealFloat fmt) (round : RoundingFunction := .tiesToEven) : RealFloat fmt :=
  match a, b with
  | .nan, _ => .nan
  | _, .nan => .nan
  | .infinity _, .infinity _ => .nan
  | .infinity s, .ofValidNNReal s' _ _ => .infinity (s * s')
  | .ofValidNNReal s _ _, .infinity s' => .ofValidNNReal (s * s') 0 (by simp)
  | .ofValidNNReal s x _, .ofValidNNReal s' x' _ =>
    if x' = 0 then
      if x = 0 then .nan else .infinity (s * s')
    else
      roundNNReal (s * s') (x / x') round

def sqrt (a : RealFloat fmt) (round : RoundingFunction := .tiesToEven) : RealFloat fmt :=
  match a with
  | .nan => .nan
  | .infinity 1 => a
  | .infinity (-1) => .nan
  | .ofValidNNReal s x _ =>
    if (s * x : ℝ) < 0 then .nan else roundReal x.sqrt s round


end LeanFloats.RealFloat
