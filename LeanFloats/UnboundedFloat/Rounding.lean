module
public import LeanFloats.UnboundedFloat.Basic
public import LeanFloats.RoundingFunction
public import Mathlib.Analysis.Real.Sqrt

@[expose] public noncomputable section

namespace LeanFloats.UnboundedFloat

variable {base : Base} {fmt : FloatFormat base}

def roundReal (x : ℝ) (zeroSign : SimpleSign := 1)
    (round : RoundingFunction := .tiesToEven) : UnboundedFloat fmt :=
  let e := fmt.getExponent x
  let x' : ℝ := round (x / base ^ e) * base ^ e
  ofValidNNReal (.ofValue x zeroSign) x'.nnabs (.abs ?_)
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
    (round : RoundingFunction := .tiesToEven) : UnboundedFloat fmt :=
  roundReal (s * x) s round

lemma roundNNReal_eq_roundReal (s x round) :
    (roundNNReal s x round : UnboundedFloat fmt) = roundReal (s * x) s round := (rfl)

variable {round : RoundingFunction}

@[simp]
lemma isFinite_roundReal (x : ℝ) (zs round) :
    (roundReal x zs round : UnboundedFloat fmt).IsFinite := by
  simp [roundReal]

@[simp]
lemma isFinite_roundNNReal (s x round) :
    (roundNNReal s x round : UnboundedFloat fmt).IsFinite := by
  simp [roundNNReal_eq_roundReal]

@[simp]
lemma sign_roundReal (x zs round) :
    (roundReal x zs round : UnboundedFloat fmt).sign = SimpleSign.ofValue x zs := by
  simp [roundReal]

@[simp]
lemma sign_roundNNReal (s x round) :
    (roundNNReal s x round : UnboundedFloat fmt).sign = s := by
  simp [roundNNReal_eq_roundReal, SimpleSign.ofValue_coe_mul_eq_self]

lemma roundReal_eq_roundReal_ofValue (x zs round) :
    (roundReal x zs round : UnboundedFloat fmt) = roundReal x (.ofValue x zs) round := by
  simp [roundReal]

lemma roundReal_eq_roundNNReal (x zs round) :
    (roundReal x zs round : UnboundedFloat fmt) = roundNNReal (.ofValue x zs) x.nnabs round := by
  simp [roundNNReal_eq_roundReal, ← roundReal_eq_roundReal_ofValue]

@[simp]
lemma neg_roundReal {x zs round} :
    -(roundReal x zs round : UnboundedFloat fmt) = roundReal (-x) (-zs) round.opposite := by
  simp [roundReal, neg_div]

@[simp]
lemma neg_roundNNReal {s x round} :
    -(roundNNReal s x round : UnboundedFloat fmt) = roundNNReal (-s) x round.opposite := by
  simp [roundNNReal_eq_roundReal]

@[simp]
lemma roundNNReal_sign_inj {s s' x round} :
    (roundNNReal s x round : UnboundedFloat fmt) = roundNNReal s' x round ↔ s = s' := by
  grind [sign_roundNNReal]

@[simp]
lemma roundReal_sign_inj {x zs zs' round} :
    (roundReal x zs round : UnboundedFloat fmt) = roundReal x zs' round ↔ x = 0 → zs = zs' := by
  simp [roundReal_eq_roundNNReal]

lemma roundReal_eq_ofValidReal {x : ℝ} (h : fmt.IsRounded x) (zs : SimpleSign) :
    roundReal x zs round = ofValidReal x h zs := by
  unfold roundReal
  extract_lets e x'
  have : x' = x := by
    unfold x'
    rw [← h.getMantissa_mul_base_pow_getExponent]
    simp [e]
  simp [this, ofValidReal]

lemma roundReal_eq_ofValidNNReal {x : NNReal} (h : fmt.IsRounded x) (s : SimpleSign) :
    roundReal (s * x) s round = ofValidNNReal s x h := by
  simp [roundReal_eq_ofValidReal (h.simpleSign_mul s), ofValidReal_def,
    SimpleSign.ofValue_coe_mul_eq_self]

lemma roundNNReal_eq_ofValidNNReal {x : NNReal} (h : fmt.IsRounded x) (s : SimpleSign) :
    roundNNReal s x round = ofValidNNReal s x h := by
  apply roundReal_eq_ofValidNNReal

lemma roundReal_eq_ofValidNNReal_pos {x : NNReal} (h : fmt.IsRounded x) :
    roundReal x 1 round = ofValidNNReal 1 x h := by
  simpa using roundReal_eq_ofValidNNReal h 1

lemma roundReal_eq_ofValidNNReal_neg {x : NNReal} (h : fmt.IsRounded x) :
    roundReal (-x) (-1) round = ofValidNNReal (-1) x h := by
  simpa using roundReal_eq_ofValidNNReal h (-1)

instance {n : Nat} : OfNat (UnboundedFloat fmt) n where
  ofNat := roundReal n

lemma ofNat_eq_roundReal_tiesToEven (n : ℕ) : (ofNat(n) : UnboundedFloat fmt) = roundReal n := (rfl)

lemma roundReal_natCast_eq_of_le {n : ℕ} (hle : (n : ℕ) ≤ base ^ fmt.precision) :
    (roundReal n : UnboundedFloat fmt) = .ofValidNNReal 1 n (fmt.isRounded_natCast hle) := by
  rw [← NNReal.coe_natCast]
  apply roundReal_eq_ofValidNNReal_pos

lemma zero_eq_ofValidNNReal : (0 : UnboundedFloat fmt) = .ofValidNNReal 1 0 (by exact fmt.isRounded_zero) := by
  rw [ofNat_eq_roundReal_tiesToEven, roundReal_natCast_eq_of_le (by simp)]
  simp

lemma one_eq_ofValidNNReal : (1 : UnboundedFloat fmt) = .ofValidNNReal 1 1 (by exact fmt.isRounded_one) := by
  rw [ofNat_eq_roundReal_tiesToEven, roundReal_natCast_eq_of_le (by simp [one_le_pow_iff])]
  simp

lemma ofValidNNReal_neg_one_eq_neg_zero :
    .ofValidNNReal (-1) 0 (by exact fmt.isRounded_zero) = (-0 : UnboundedFloat fmt) := by
  simp [zero_eq_ofValidNNReal]

@[simp]
lemma ofValidNNReal_eq_zero_iff {s x h} :
    (.ofValidNNReal s x h : UnboundedFloat fmt) = 0 ↔ s = 1 ∧ x = 0 := by
  simp [zero_eq_ofValidNNReal]

@[simp]
lemma ofValidNNReal_eq_neg_zero_iff {s x h} :
    (.ofValidNNReal s x h : UnboundedFloat fmt) = -0 ↔ s = -1 ∧ x = 0 := by
  simp [zero_eq_ofValidNNReal]

@[simp] lemma isFinite_ofNat {n} : (ofNat(n) : UnboundedFloat fmt).IsFinite := by simp [ofNat_eq_roundReal_tiesToEven]

@[simp] lemma toEReal_zero : (0 : UnboundedFloat fmt).toEReal = 0 := by simp [zero_eq_ofValidNNReal]
@[simp] lemma toEReal_one : (1 : UnboundedFloat fmt).toEReal = 1 := by simp [one_eq_ofValidNNReal]

@[simp] lemma toFiniteReal_zero : (0 : UnboundedFloat fmt).toFiniteReal = 0 := by simp [zero_eq_ofValidNNReal]
@[simp] lemma toFiniteReal_one : (1 : UnboundedFloat fmt).toFiniteReal = 1 := by simp [one_eq_ofValidNNReal]

@[simp] lemma toReal_zero : (0 : UnboundedFloat fmt).toReal = 0 := by simp [zero_eq_ofValidNNReal]
@[simp] lemma toReal_one : (1 : UnboundedFloat fmt).toReal = 1 := by simp [one_eq_ofValidNNReal]

@[simp] lemma sign_ofNat {n : Nat} : (ofNat(n) : UnboundedFloat fmt).sign = 1 := by
  simp [ofNat_eq_roundReal_tiesToEven, SimpleSign.ofValue_of_nonneg]

@[simp]
lemma neg_zero_equiv_zero : (-0 : UnboundedFloat fmt) ≈ 0 := by
  rw [UnboundedFloat.equiv_def]
  simp

@[simp]
lemma zero_equiv_neg_zero : (0 : UnboundedFloat fmt) ≈ -0 := by
  rw [UnboundedFloat.equiv_def]
  simp

lemma equiv_cases {a b : UnboundedFloat fmt} :
    a ≈ b ↔ (a ≠ nan ∧ a = b) ∨ (a = 0 ∧ b = -0) ∨ (a = -0 ∧ b = 0) := by
  constructor
  · intro h
    rw [UnboundedFloat.equiv_def] at h
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

lemma ext_toEReal_sign {a b : UnboundedFloat fmt}
    (h₁ : a.toEReal = b.toEReal) (h₂ : a.sign = b.sign) : a = b := by
  by_cases ha : a = nan
  · simp_all [eq_comm (a := (0 : SignType))]
  by_cases hb : b = nan
  · simp_all
  have eqv : a ≈ b := by simp [UnboundedFloat.equiv_def, *]
  rw [equiv_cases] at eqv
  obtain ⟨_, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := eqv <;> simp_all

/-! Addition -/

protected def add (a b : UnboundedFloat fmt) (round : RoundingFunction := .tiesToEven) : UnboundedFloat fmt :=
  match a, b with
  | .nan, _ => .nan
  | _, .nan => .nan
  | .infinity s, .infinity s' =>
    if s = s' then a else .nan
  | .infinity _, _ => a
  | _, .infinity _ => b
  | .ofValidNNReal s x _, .ofValidNNReal s' x' _ =>
    roundReal (s * x + s' * x') (max s s') round

@[simp] lemma nan_add (a : UnboundedFloat fmt) (round : RoundingFunction) : nan.add a round = nan := (rfl)

@[simp] lemma add_nan (a : UnboundedFloat fmt) (round : RoundingFunction) : a.add nan round = nan := by cases a <;> rfl

@[simp] lemma infinity_add_self (s : SimpleSign) (round : RoundingFunction) :
    (infinity s : UnboundedFloat fmt).add (infinity s) round = infinity s := by cases s <;> rfl

@[simp] lemma infinity_add_neg (s : SimpleSign) (round : RoundingFunction) :
    (infinity s : UnboundedFloat fmt).add (infinity (-s)) round = nan := by cases s <;> rfl

@[simp] lemma infinity_neg_add (s : SimpleSign) (round : RoundingFunction) :
    (infinity (-s) : UnboundedFloat fmt).add (infinity s) round = nan := by cases s <;> rfl

lemma infinity_add_infinity (s s' : SimpleSign) (round : RoundingFunction) :
    (infinity s : UnboundedFloat fmt).add (infinity s') round = if s = s' then infinity s else .nan := (rfl)

@[simp] lemma infinity_add_ofValidNNReal (s : SimpleSign) (s' x h) (round : RoundingFunction) :
    (infinity s : UnboundedFloat fmt).add (ofValidNNReal s' x h) round = infinity s := (rfl)

@[simp] lemma ofValidNNReal_add_infinity (s x h) (s' : SimpleSign) (round : RoundingFunction) :
    (ofValidNNReal s x h : UnboundedFloat fmt).add (infinity s') round = infinity s' := (rfl)

protected lemma IsFinite.add {f f' : UnboundedFloat fmt} (hf : IsFinite f) (hf' : IsFinite f') :
    (f.add f' round).IsFinite := by
  cases hf; cases hf'; simp [UnboundedFloat.add]

lemma IsFinite.infinity_add {f : UnboundedFloat fmt} (h : IsFinite f) (s : SimpleSign) (round) :
    (infinity s).add f round = infinity s := by cases h; simp

lemma IsFinite.add_infinity {f : UnboundedFloat fmt} (h : IsFinite f) (s : SimpleSign) (round) :
    f.add (infinity s : UnboundedFloat fmt) round = infinity s := by cases h; simp

lemma ofValidNNReal_add_ofValidNNReal (s x h) (s' x' h') (round : RoundingFunction) :
    (ofValidNNReal s x h : UnboundedFloat fmt).add (ofValidNNReal s' x' h') round =
      roundReal (s * x + s' * x') (max s s') round := (rfl)

protected lemma add_comm (a b : UnboundedFloat fmt) (round : RoundingFunction) :
    a.add b round = b.add a round := by
  cases a <;> cases b <;>
    simp +contextual [infinity_add_infinity, ofValidNNReal_add_ofValidNNReal,
      add_comm, max_comm, eq_comm]

@[simp]
protected lemma add_neg_zero (a : UnboundedFloat fmt) (round : RoundingFunction) :
    a.add (-0) round = a := by
  rw [zero_eq_ofValidNNReal, neg_ofValidNNReal]
  cases a
  · rename_i s _ h
    cases s <;> simp [ofValidNNReal_add_ofValidNNReal, roundReal_eq_ofValidNNReal_pos h,
      roundReal_eq_ofValidNNReal_neg h]
  · simp
  · simp

@[simp]
protected lemma neg_zero_add (a : UnboundedFloat fmt) (round : RoundingFunction) :
    (-0 : UnboundedFloat fmt).add a round = a := by
  rw [UnboundedFloat.add_comm, UnboundedFloat.add_neg_zero]

lemma add_zero_eq_ite {a : UnboundedFloat fmt} {round : RoundingFunction} :
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
lemma zero_add_zero {round : RoundingFunction} : (0 : UnboundedFloat fmt).add 0 round = 0 := by
  simp [add_zero_eq_ite]

lemma zero_add_eq_ite {a : UnboundedFloat fmt} {round : RoundingFunction} :
    (0 : UnboundedFloat fmt).add a round = if a = -0 then 0 else a := by
  rw [UnboundedFloat.add_comm, add_zero_eq_ite]

lemma add_zero_equiv {a : UnboundedFloat fmt} {round : RoundingFunction}
    (h : a ≠ nan) : a.add 0 round ≈ a := by
  rw [add_zero_eq_ite]
  split <;> simp_all

lemma zero_add_equiv {a : UnboundedFloat fmt} {round : RoundingFunction}
    (h : a ≠ nan) : (0 : UnboundedFloat fmt).add a round ≈ a := by
  rw [UnboundedFloat.add_comm]
  exact UnboundedFloat.add_zero_equiv h

/-
@[gcongr]
protected lemma add_equiv {a b c d : UnboundedFloat fmt} {round : RoundingFunction}
    (hab : a ≈ b) (hcd : c ≈ d) : a.add c round ≈ b.add d round := by
  rw [UnboundedFloat.equiv_cases] at hab hcd
  obtain ⟨ha, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hab <;>
    obtain ⟨ha, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hcd <;>
    simp [*, add_zero_equiv, zero_add_equiv, equiv_comm (b := add _ _ _)]
-/

@[simp]
def sub (a b : UnboundedFloat fmt) (round : RoundingFunction := .tiesToEven) : UnboundedFloat fmt :=
  a.add (-b) round

def mul (a b : UnboundedFloat fmt) (round : RoundingFunction := .tiesToEven) : UnboundedFloat fmt :=
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

def div (a b : UnboundedFloat fmt) (round : RoundingFunction := .tiesToEven) : UnboundedFloat fmt :=
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

def sqrt (a : UnboundedFloat fmt) (round : RoundingFunction := .tiesToEven) : UnboundedFloat fmt :=
  match a with
  | .nan => .nan
  | .infinity 1 => a
  | .infinity (-1) => .nan
  | .ofValidNNReal s x _ =>
    if (s * x : ℝ) < 0 then .nan else roundReal x.sqrt s round


end LeanFloats.UnboundedFloat
