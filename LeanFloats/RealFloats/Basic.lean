module
public import LeanFloats.FloatFormat
public import LeanFloats.ForMathlib

@[expose] public section

noncomputable section

namespace LeanFloats

variable {base : Base}

inductive RealFloat (fmt : FloatFormat base) where
  | ofValidNNReal (s : SimpleSign) (x : NNReal) (h : fmt.IsValidFloat x)
  | infinity (s : SimpleSign)
  | nan
deriving DecidableEq

namespace RealFloat

variable {fmt : FloatFormat base}

def toReal : RealFloat fmt → ℝ
  | .ofValidNNReal s x _h => s * x
  | .infinity s => s * base ^ fmt.infExp
  | .nan => 0

def toEReal : RealFloat fmt → EReal
  | .ofValidNNReal s x _h => s * x
  | .infinity s => s * ⊤
  | .nan => 0

def ofValidReal (x : ℝ) (h : fmt.IsValidFloat x) (zeroSign : SimpleSign := 1) :
    RealFloat fmt :=
  .ofValidNNReal (.ofValue x zeroSign) x.nnabs (by simpa using h.abs)

def ofValidEReal (x : EReal) (h : fmt.IsValidFloat x.toReal) (zeroSign : SimpleSign := 1) :
    RealFloat fmt :=
  match x with
  | ⊤ => .infinity 1
  | ⊥ => .infinity (-1)
  | (x : ℝ) => .ofValidReal x h zeroSign

inductive IsFinite : RealFloat fmt → Prop where
  | ofValidNNReal (s : SimpleSign) (x : NNReal) (h) :
    IsFinite (ofValidNNReal s x h)

attribute [simp] IsFinite.ofValidNNReal

@[simp]
lemma isFinite_ofValidReal (x : ℝ) (h : fmt.IsValidFloat x) (zs : SimpleSign) :
    IsFinite (ofValidReal x h zs) :=
  .ofValidNNReal ..

@[simp]
lemma not_isFinite_nan : ¬ IsFinite (nan : RealFloat fmt) := nofun

@[simp]
lemma not_isFinite_infinity {s : SimpleSign} : ¬ IsFinite (infinity s : RealFloat fmt) := nofun

@[simp]
lemma IsFinite.ne_nan {x : RealFloat fmt} (h : x.IsFinite) : x ≠ nan := by
  cases h; simp

@[simp]
lemma IsFinite.ne_infinity {x : RealFloat fmt} {s : SimpleSign}
    (h : x.IsFinite) : x ≠ infinity s := by
  cases h; simp

@[simp]
lemma IsFinite.infinity_ne {x : RealFloat fmt} {s : SimpleSign}
    (h : x.IsFinite) : infinity s ≠ x := by
  cases h; simp

@[simp]
lemma ofValidReal_ne_nan (x : ℝ) (h : fmt.IsValidFloat x) (zs : SimpleSign) :
    ofValidReal x h zs ≠ nan := (isFinite_ofValidReal x h zs).ne_nan

@[simp]
lemma toReal_nan : (nan : RealFloat fmt).toReal = 0 := rfl

@[simp]
lemma toReal_infinity : (infinity s : RealFloat fmt).toReal = s * base ^ fmt.infExp := rfl

@[simp]
lemma toReal_ofValidNNReal (s : SimpleSign) (x : NNReal) (h : fmt.IsValidFloat x) :
    (ofValidNNReal s x h).toReal = s * x := (rfl)

@[simp]
lemma toReal_ofValidReal (x : ℝ) (h : fmt.IsValidFloat x) (zs : SimpleSign) :
    (ofValidReal x h zs).toReal = x := by
  simp [ofValidReal]

@[simp]
lemma toEReal_nan : (nan : RealFloat fmt).toEReal = 0 := rfl

@[simp]
lemma toEReal_infinity : (infinity s : RealFloat fmt).toEReal = s * ⊤ := rfl

@[simp]
lemma toEReal_ofValidNNReal (s : SimpleSign) (x : NNReal) (h : fmt.IsValidFloat x) :
    (ofValidNNReal s x h).toEReal = s * x := (rfl)

lemma toEReal_eq_toReal_of_isFinite {x : RealFloat fmt} (h : IsFinite x) :
    x.toEReal = x.toReal := by
  cases h; simp [ENNReal.toEReal]

@[simp]
lemma toEReal_ofValidReal (x : ℝ) (h : fmt.IsValidFloat x) (zs : SimpleSign) :
    (ofValidReal x h zs).toEReal = x := by
  simp [toEReal_eq_toReal_of_isFinite]

lemma ofValidReal_def (x : ℝ) (h : fmt.IsValidFloat x) (zs : SimpleSign) :
    ofValidReal x h zs = ofValidNNReal (.ofValue x zs) x.nnabs (by simpa using h.abs) := (rfl)

@[simp]
lemma ofValidEReal_top (zs : SimpleSign) :
    (ofValidEReal ⊤ (by simp) zs : RealFloat fmt) = .infinity 1 := rfl

@[simp]
lemma ofValidEReal_bot (zs : SimpleSign) :
    (ofValidEReal ⊥ (by simp) zs : RealFloat fmt) = .infinity (-1) := rfl

@[simp]
lemma ofValidEReal_ofReal (x : ℝ) (h) (zs : SimpleSign) :
    (ofValidEReal x h zs : RealFloat fmt) = .ofValidReal x (id h) zs := rfl

@[simp]
lemma toEReal_ofValidEReal (x : EReal) (h : fmt.IsValidFloat x.toReal) (zs : SimpleSign) :
    (ofValidEReal x h zs).toEReal = x := by
  cases x <;> simp

@[simp]
lemma ofValidEReal_ne_nan (x : EReal) (h : fmt.IsValidFloat x.toReal) (zs : SimpleSign) :
    ofValidEReal x h zs ≠ nan := by
  cases x <;> simp

instance : LE (RealFloat fmt) where
  le a b := a ≠ nan ∧ b ≠ nan ∧ a.toEReal ≤ b.toEReal

protected def Equiv (a b : RealFloat fmt) : Prop :=
  a ≠ nan ∧ b ≠ nan ∧ a.toEReal = b.toEReal

instance : HasEquiv (RealFloat fmt) where
  Equiv a b := a.Equiv b

noncomputable instance : DecidableLE (RealFloat fmt) := fun _ _ => Classical.propDecidable _
noncomputable instance (a b : RealFloat fmt) : Decidable (a ≈ b) := Classical.propDecidable _

instance : BEq (RealFloat fmt) where
  beq a b := a ≈ b

@[grind =]
protected lemma le_def {a b : RealFloat fmt} : a ≤ b ↔ a ≠ nan ∧ b ≠ nan ∧ a.toEReal ≤ b.toEReal := (Iff.rfl)

@[grind =]
protected lemma equiv_def {a b : RealFloat fmt} : a ≈ b ↔ a ≠ nan ∧ b ≠ nan ∧ a.toEReal = b.toEReal := (Iff.rfl)

@[simp] protected lemma beq_def (a b : RealFloat fmt) : (a == b) = decide (a ≈ b) := (rfl)
@[simp] protected lemma bne_def (a b : RealFloat fmt) : (a != b) = !decide (a ≈ b) := (rfl)

protected lemma le_trans {a b c : RealFloat fmt} (h : a ≤ b) (h' : b ≤ c) : a ≤ c := by grind
protected lemma le_antisymm {a b : RealFloat fmt} (h : a ≤ b) (h' : b ≤ a) : a ≈ b := by grind
protected lemma le_antisymm_iff {a b : RealFloat fmt} : a ≈ b ↔ a ≤ b ∧ b ≤ a := by grind

@[trans] lemma equiv_trans {a b c : RealFloat fmt} (h : a ≈ b) (h' : b ≈ c) : a ≈ c := by grind
@[symm] lemma equiv_symm {a b : RealFloat fmt} (h : a ≈ b) : b ≈ a := by grind
lemma equiv_comm {a b : RealFloat fmt} : a ≈ b ↔ b ≈ a := by grind

@[gcongr] lemma equiv_iff_equiv {a b c d : RealFloat fmt} (hac : a ≈ c) (hbd : b ≈ d) : a ≈ b ↔ c ≈ d := by grind
@[gcongr] lemma equiv_iff_equiv_left {a b c : RealFloat fmt} (hac : a ≈ c) : a ≈ b ↔ c ≈ b := by grind
@[gcongr] lemma equiv_iff_equiv_right {a b c : RealFloat fmt} (hac : b ≈ c) : a ≈ b ↔ a ≈ c := by grind

@[gcongr] lemma equiv_imp_equiv {a b c d : RealFloat fmt} (hac : a ≈ c) (hbd : b ≈ d) : a ≈ b → c ≈ d := by grind
@[gcongr] lemma equiv_imp_equiv_left {a b c : RealFloat fmt} (hac : a ≈ c) : a ≈ b → c ≈ b := by grind
@[gcongr] lemma equiv_imp_equiv_right {a b c : RealFloat fmt} (hac : b ≈ c) : a ≈ b → a ≈ c := by grind

@[simp] lemma equiv_self_iff_ne_nan {a : RealFloat fmt} : a ≈ a ↔ a ≠ nan := by grind

instance : @Trans (RealFloat fmt) _ _ (· ≈ ·) (· ≈ ·) (· ≈ ·) := ⟨RealFloat.equiv_trans⟩
instance : @Std.Symm (RealFloat fmt) (· ≈ ·) := ⟨fun _ _ => RealFloat.equiv_symm⟩

@[simp] lemma not_nan_le {a : RealFloat fmt} : ¬nan ≤ a := by grind
@[simp] lemma not_le_nan {a : RealFloat fmt} : ¬a ≤ nan := by grind
@[simp] lemma not_nan_equiv {a : RealFloat fmt} : ¬nan ≈ a := by grind
@[simp] lemma not_equiv_nan {a : RealFloat fmt} : ¬a ≈ nan := by grind

protected lemma le_total {a b : RealFloat fmt} (ha : a ≠ nan) (hb : b ≠ nan) : a ≤ b ∨ b ≤ a := by grind

protected def neg : RealFloat fmt → RealFloat fmt
  | .ofValidNNReal s x h => .ofValidNNReal (-s) x h
  | .infinity s => .infinity (-s)
  | .nan => .nan

instance : Neg (RealFloat fmt) where
  neg := RealFloat.neg

@[simp] lemma neg_ofValidNNReal {s x h} : -(ofValidNNReal s x h : RealFloat fmt) = ofValidNNReal (-s) x h := rfl
@[simp] lemma neg_infinity {s} : -(infinity s : RealFloat fmt) = infinity (-s) := rfl
@[simp] lemma neg_nan : -(nan : RealFloat fmt) = nan := rfl

instance : InvolutiveNeg (RealFloat fmt) where
  neg_neg x := by cases x <;> simp

@[simp] lemma neg_eq_nan_iff {x : RealFloat fmt} : -x = nan ↔ x = nan := by simp [neg_eq_iff_eq_neg]
@[simp] lemma neg_eq_self_iff {x : RealFloat fmt} : -x = x ↔ x = nan := by cases x <;> simp
@[simp] lemma self_eq_neg_iff {x : RealFloat fmt} : x = -x ↔ x = nan := by cases x <;> simp

@[simp] lemma isFinite_neg_iff {x : RealFloat fmt} : IsFinite (-x) ↔ IsFinite x := by cases x <;> simp

@[simp] lemma neg_ofValidReal {x h zs} :
    -(ofValidReal x h zs : RealFloat fmt) = ofValidReal (-x) h.neg (-zs) := by
  simp [ofValidReal]

@[simp]
lemma toReal_neg (x : RealFloat fmt) : (-x).toReal = -x.toReal := by
  cases x <;> simp

@[simp]
lemma toEReal_neg (x : RealFloat fmt) : (-x).toEReal = -x.toEReal := by
  cases x <;> simp

def sign (x : RealFloat fmt) : SignType :=
  match x with
  | .ofValidNNReal s _ _ => s
  | .infinity s => s
  | .nan => 0

@[simp] lemma sign_ofValidNNReal {s x h} : (ofValidNNReal s x h : RealFloat fmt).sign = s := rfl
@[simp] lemma sign_infinity {s} : (infinity s : RealFloat fmt).sign = s := rfl
@[simp] lemma sign_nan : (nan : RealFloat fmt).sign = 0 := rfl

@[simp] lemma sign_ofValidReal {x h zs} :
    (ofValidReal x h zs : RealFloat fmt).sign = SimpleSign.ofValue x zs := (rfl)
@[simp] lemma sign_ofValidEReal {x h zs} :
    (ofValidEReal x h zs : RealFloat fmt).sign = SimpleSign.ofValue x zs := by
  cases x <;> simp [SimpleSign.ofValue_of_neg, SimpleSign.ofValue_of_pos]

@[simp] lemma sign_neg (x : RealFloat fmt) : (-x).sign = -x.sign := by cases x <;> simp
@[simp] lemma sign_eq_zero_iff {x : RealFloat fmt} : x.sign = 0 ↔ x = nan := by cases x <;> simp

end LeanFloats.RealFloat
