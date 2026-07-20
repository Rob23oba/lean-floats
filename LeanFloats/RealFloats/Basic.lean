module
public import LeanFloats.UnboundedFloat.Basic

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

@[coe]
def toUnbounded : RealFloat fmt → UnboundedFloat fmt
  | .ofValidNNReal s x h => .ofValidNNReal s x h.1
  | .infinity s => .infinity s
  | .nan => .nan

instance : Coe (RealFloat fmt) (UnboundedFloat fmt) where
  coe := toUnbounded

def toReal : RealFloat fmt → ℝ
  | .ofValidNNReal s x _h => s * x
  | .infinity s => s * base ^ fmt.infExp
  | .nan => 0

def toFiniteReal : RealFloat fmt → ℝ
  | .ofValidNNReal s x _h => s * x
  | .infinity _ => 0
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

@[simp low]
lemma IsFinite.ne_nan {x : RealFloat fmt} (h : x.IsFinite) : x ≠ nan := by
  cases h; simp

@[simp low]
lemma IsFinite.ne_infinity {x : RealFloat fmt} {s : SimpleSign}
    (h : x.IsFinite) : x ≠ infinity s := by
  cases h; simp

@[simp low]
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
lemma toFiniteReal_nan : (nan : RealFloat fmt).toFiniteReal = 0 := rfl

@[simp]
lemma toFiniteReal_infinity : (infinity s : RealFloat fmt).toFiniteReal = 0 := rfl

@[simp]
lemma toFiniteReal_ofValidNNReal (s : SimpleSign) (x : NNReal) (h : fmt.IsValidFloat x) :
    (ofValidNNReal s x h).toFiniteReal = s * x := (rfl)

@[simp]
lemma toFiniteReal_ofValidReal (x : ℝ) (h : fmt.IsValidFloat x) (zs : SimpleSign) :
    (ofValidReal x h zs).toFiniteReal = x := by
  simp [ofValidReal]

@[simp]
lemma isValidFloat_toFiniteReal (x : RealFloat fmt) :
    fmt.IsValidFloat x.toFiniteReal := by
  cases x <;> simp [*]

@[simp]
lemma isRounded_toFiniteReal (x : RealFloat fmt) :
    fmt.IsRounded x.toFiniteReal := (isValidFloat_toFiniteReal x).isRounded

@[simp]
lemma inRange_toFiniteReal (x : RealFloat fmt) :
    fmt.InRange x.toFiniteReal := (isValidFloat_toFiniteReal x).inRange

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
lemma toFiniteReal_ofValidEReal (x : EReal) (h : fmt.IsValidFloat x.toReal) (zs : SimpleSign) :
    (ofValidEReal x h zs).toFiniteReal = x.toReal := by
  cases x <;> simp

@[simp]
lemma toReal_toEReal (x : RealFloat fmt) : x.toEReal.toReal = x.toFiniteReal := by
  cases x <;> (try cases ‹SimpleSign›) <;> simp

@[simp]
lemma ofValidEReal_ne_nan (x : EReal) (h : fmt.IsValidFloat x.toReal) (zs : SimpleSign) :
    ofValidEReal x h zs ≠ nan := by
  cases x <;> simp


@[simp, norm_cast]
lemma toUnbounded_ofValidNNReal {s : SimpleSign} {x : NNReal} (h : fmt.IsValidFloat x) :
    (ofValidNNReal s x h).toUnbounded = .ofValidNNReal s x h.1 := (rfl)

@[simp, norm_cast]
lemma toUnbounded_infinity (s : SimpleSign) :
    (infinity s : RealFloat fmt).toUnbounded = .infinity s := (rfl)

@[simp, norm_cast]
lemma toUnbounded_nan : (nan : RealFloat fmt).toUnbounded = .nan := (rfl)

@[simp, norm_cast]
lemma toUnbounded_ofValidReal {x : Real} {zs : SimpleSign} (h : fmt.IsValidFloat x) :
    (ofValidReal x h zs).toUnbounded = .ofValidReal x h.1 zs := (rfl)

@[simp, norm_cast]
lemma toUnbounded_ofValidEReal {x : EReal} {zs : SimpleSign} (h : fmt.IsValidFloat x.toReal) :
    (ofValidEReal x h zs).toUnbounded = .ofValidEReal x h.1 zs := by
  cases x <;> simp

@[simp, norm_cast]
lemma toReal_toUnbounded {x : RealFloat fmt} : x.toUnbounded.toReal = x.toReal := by
  cases x <;> simp

@[simp, norm_cast]
lemma toFiniteReal_toUnbounded {x : RealFloat fmt} : x.toUnbounded.toFiniteReal = x.toFiniteReal := by
  cases x <;> simp

@[simp, norm_cast]
lemma toEReal_toUnbounded {x : RealFloat fmt} : x.toUnbounded.toEReal = x.toEReal := by
  cases x <;> simp

@[simp, norm_cast]
lemma isFinite_toUnbounded_iff {x : RealFloat fmt} :
    x.toUnbounded.IsFinite ↔ x.IsFinite := by cases x <;> simp

@[simp, norm_cast]
lemma toUnbounded_inj {x y : RealFloat fmt} : x.toUnbounded = y.toUnbounded ↔ x = y := by
  cases x <;> cases y <;> simp

@[simp, norm_cast]
lemma toUnbounded_eq_nan_iff {x : RealFloat fmt} : x.toUnbounded = .nan ↔ x = nan :=
  toUnbounded_inj (y := nan)

@[simp, norm_cast]
lemma toUnbounded_eq_infinity_iff {x : RealFloat fmt} {s : SimpleSign} :
    x.toUnbounded = .infinity s ↔ x = infinity s :=
  toUnbounded_inj (y := infinity s)


def ofUnboundedInRange (x : UnboundedFloat fmt) (h : fmt.InRange x.toFiniteReal) : RealFloat fmt :=
  match x with
  | .ofValidNNReal s x hr => .ofValidNNReal s x ⟨hr, by simpa using h⟩
  | .infinity s => .infinity s
  | .nan => .nan

@[simp]
lemma ofUnboundedInRange_ofValidNNReal {s : SimpleSign} {x : NNReal} (h : fmt.IsRounded x) (h') :
    ofUnboundedInRange (.ofValidNNReal s x h) h' = .ofValidNNReal s x ⟨h, by simpa using h'⟩ :=
  (rfl)

@[simp]
lemma ofUnboundedInRange_infinity (s : SimpleSign) :
    ofUnboundedInRange (.infinity s : UnboundedFloat fmt) (by simp) = infinity s := (rfl)

@[simp]
lemma ofUnboundedInRange_nan :
    ofUnboundedInRange (.nan : UnboundedFloat fmt) (by simp) = nan := (rfl)

@[simp, norm_cast]
lemma toUnbounded_ofUnboundedInRange {x : UnboundedFloat fmt} (h : fmt.InRange x.toFiniteReal) :
    (ofUnboundedInRange x h).toUnbounded = x := by
  cases x <;> simp

@[simp, norm_cast]
lemma ofUnboundedInRange_toUnbounded (x : RealFloat fmt) :
    ofUnboundedInRange x (by simp) = x := by
  cases x <;> simp

@[simp]
lemma ofUnboundedInRange_ofValidReal {x : Real} {zs : SimpleSign} (h : fmt.IsRounded x) (h') :
    ofUnboundedInRange (.ofValidReal x h zs) h' = .ofValidReal x ⟨h, by simpa using h'⟩ zs :=
  (rfl)

@[simp]
lemma ofUnboundedInRange_ofValidEReal {x : EReal} {zs : SimpleSign} (h : fmt.IsRounded x.toReal) (h') :
    ofUnboundedInRange (.ofValidEReal x h zs) h' = .ofValidEReal x ⟨h, by simpa using h'⟩ zs := by
  simp [← toUnbounded_inj]

@[simp]
lemma toReal_ofUnboundedInRange {x : UnboundedFloat fmt} (h : fmt.InRange x.toFiniteReal) :
    (ofUnboundedInRange x h).toReal = x.toReal := by
  cases x <;> simp

@[simp]
lemma toFiniteReal_ofUnboundedInRange {x : UnboundedFloat fmt} (h : fmt.InRange x.toFiniteReal) :
    (ofUnboundedInRange x h).toFiniteReal = x.toFiniteReal := by
  cases x <;> simp

@[simp]
lemma toEReal_ofUnboundedInRange {x : UnboundedFloat fmt} (h : fmt.InRange x.toFiniteReal) :
    (ofUnboundedInRange x h).toEReal = x.toEReal := by
  cases x <;> simp

@[simp]
lemma isFinite_ofUnboundedInRange_iff {x : UnboundedFloat fmt} (h : fmt.InRange x.toFiniteReal) :
    (ofUnboundedInRange x h).IsFinite ↔ x.IsFinite := by
  cases x <;> simp

@[simp]
lemma ofUnboundedInRange_inj {x y : UnboundedFloat fmt} (h h') :
    ofUnboundedInRange x h = ofUnboundedInRange y h' ↔ x = y := by
  cases x <;> cases y <;> simp

@[simp]
lemma ofUnboundedInRange_eq_nan_iff {x : UnboundedFloat fmt} (h) :
    ofUnboundedInRange x h = nan ↔ x = .nan := by
  simp [← toUnbounded_inj]

@[simp]
lemma ofUnboundedInRange_eq_infinity_iff {x : UnboundedFloat fmt} {s : SimpleSign} (h) :
    ofUnboundedInRange x h = infinity s ↔ x = .infinity s := by
  simp [← toUnbounded_inj]

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

@[simp, norm_cast]
lemma toUnbounded_le {x y : RealFloat fmt} : x.toUnbounded ≤ y.toUnbounded ↔ x ≤ y := by
  simp [RealFloat.le_def, UnboundedFloat.le_def]

@[simp, norm_cast]
lemma toUnbounded_equiv {x y : RealFloat fmt} : x.toUnbounded ≈ y.toUnbounded ↔ x ≈ y := by
  simp [RealFloat.equiv_def, UnboundedFloat.equiv_def]

@[simp]
lemma ofUnboundedInRange_le {x y : UnboundedFloat fmt}
    (hx : fmt.InRange x.toFiniteReal) (hy : fmt.InRange y.toFiniteReal) :
    ofUnboundedInRange x hx ≤ ofUnboundedInRange y hy ↔ x ≤ y := by
  simp [← toUnbounded_le]

@[simp]
lemma ofUnboundedInRange_equiv {x y : UnboundedFloat fmt}
    (hx : fmt.InRange x.toFiniteReal) (hy : fmt.InRange y.toFiniteReal) :
    ofUnboundedInRange x hx ≈ ofUnboundedInRange y hy ↔ x ≈ y := by
  simp [← toUnbounded_equiv]

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

@[simp, norm_cast]
lemma toUnbounded_neg (x : RealFloat fmt) : (-x).toUnbounded = -x.toUnbounded := by
  cases x <;> simp

@[simp]
lemma neg_ofUnboundedInRange {x : UnboundedFloat fmt} (h : fmt.InRange x.toFiniteReal) :
    -ofUnboundedInRange x h = ofUnboundedInRange (-x) (by simpa using h) := by
  cases x <;> simp

instance : InvolutiveNeg (RealFloat fmt) where
  neg_neg x := by cases x <;> simp

@[simp] lemma neg_eq_nan_iff {x : RealFloat fmt} : -x = nan ↔ x = nan := by simp [neg_eq_iff_eq_neg]
@[simp] lemma neg_eq_self_iff {x : RealFloat fmt} : -x = x ↔ x = nan := by cases x <;> simp
@[simp] lemma self_eq_neg_iff {x : RealFloat fmt} : x = -x ↔ x = nan := by cases x <;> simp

@[simp] lemma isFinite_neg_iff {x : RealFloat fmt} : IsFinite (-x) ↔ IsFinite x := by cases x <;> simp

@[simp] lemma neg_ofValidReal {x h zs} :
    -(ofValidReal x h zs : RealFloat fmt) = ofValidReal (-x) h.neg (-zs) := by
  simp [← toUnbounded_inj]

@[simp] lemma neg_ofValidEReal {x h zs} :
    -(ofValidEReal x h zs : RealFloat fmt) = ofValidEReal (-x) (by simpa using h.neg) (-zs) := by
  simp [← toUnbounded_inj]

@[simp]
lemma toReal_neg (x : RealFloat fmt) : (-x).toReal = -x.toReal := by
  simp [← toReal_toUnbounded]

@[simp]
lemma toEReal_neg (x : RealFloat fmt) : (-x).toEReal = -x.toEReal := by
  simp [← toEReal_toUnbounded]

def sign (x : RealFloat fmt) : SignType :=
  match x with
  | .ofValidNNReal s _ _ => s
  | .infinity s => s
  | .nan => 0

@[simp] lemma sign_ofValidNNReal {s x h} : (ofValidNNReal s x h : RealFloat fmt).sign = s := rfl
@[simp] lemma sign_infinity {s} : (infinity s : RealFloat fmt).sign = s := rfl
@[simp] lemma sign_nan : (nan : RealFloat fmt).sign = 0 := rfl

@[simp, norm_cast]
lemma sign_toUnbounded {x : RealFloat fmt} : x.toUnbounded.sign = x.sign := by
  cases x <;> simp

@[simp]
lemma sign_ofUnboundedInRange {x : UnboundedFloat fmt} (h) :
    (ofUnboundedInRange x h).sign = x.sign := by
  cases x <;> simp

@[simp] lemma sign_ofValidReal {x h zs} :
    (ofValidReal x h zs : RealFloat fmt).sign = SimpleSign.ofValue x zs := (rfl)
@[simp] lemma sign_ofValidEReal {x h zs} :
    (ofValidEReal x h zs : RealFloat fmt).sign = SimpleSign.ofValue x zs := by
  simp [← sign_toUnbounded]

@[simp] lemma sign_neg (x : RealFloat fmt) : (-x).sign = -x.sign := by cases x <;> simp
@[simp] lemma sign_eq_zero_iff {x : RealFloat fmt} : x.sign = 0 ↔ x = nan := by cases x <;> simp

end LeanFloats.RealFloat
