module
public import LeanFloats.ForMathlib

@[expose] public section

namespace LeanFloats

inductive SimpleSign where
  | one
  | negOne

@[inline]
instance : DecidableEq SimpleSign := fun
  | .one, .one => isTrue rfl
  | .negOne, .one => isFalse nofun
  | .one, .negOne => isFalse nofun
  | .negOne, .negOne => isTrue rfl

namespace SimpleSign

instance : One SimpleSign where
  one := .one

instance : Neg SimpleSign where
  neg
    | .one => .negOne
    | .negOne => .one

instance : Mul SimpleSign where
  mul
    | .one, .one => .one
    | .one, .negOne => .negOne
    | .negOne, .one => .negOne
    | .negOne, .negOne => .one

instance : Inv SimpleSign where
  inv x := x

@[cases_eliminator, induction_eliminator]
lemma cases {motive : SimpleSign → Prop} (one : motive 1) (neg_one : motive (-1))
    (t : SimpleSign) : motive t := by
  cases t <;> assumption

protected lemma forall_iff {p : SimpleSign → Prop} :
    (∀ s, p s) ↔ p 1 ∧ p (-1) := by
  constructor
  · intro h
    simp [h]
  · rintro ⟨h, h'⟩ (_ | _) <;> assumption

instance {p : SimpleSign → Prop} [DecidablePred p] : Decidable (∀ s, p s) :=
  decidable_of_decidable_of_iff SimpleSign.forall_iff.symm

instance : CommGroup SimpleSign where
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide
  inv_mul_cancel := by decide
  npow n
    | .one => .one
    | .negOne => if 2 ∣ n then .one else .negOne
  npow_zero := by decide
  npow_succ := by simp [· * ·, Mul.mul, · ^ ·, Pow.pow]; grind
  zpow n
    | .one => .one
    | .negOne => if 2 ∣ n then .one else .negOne
  zpow_zero' := by decide
  zpow_neg' := by simp [Inv.inv, · ^ ·, Pow.pow]
  zpow_succ' := by simp [· * ·, Mul.mul, · ^ ·, Pow.pow]; grind

@[simp] lemma one_eq : one = 1 := rfl
@[simp] lemma negOne_eq : negOne = -1 := rfl

@[simp] protected lemma mul_self : ∀ (s : SimpleSign), s * s = 1 := by decide
@[simp] protected lemma mul_self_right : ∀ (s s' : SimpleSign), s * s' * s' = s := by decide
@[simp] protected lemma mul_self_left : ∀ (s s' : SimpleSign), s * (s * s') = s' := by decide
@[simp high] protected lemma inv_eq_self : ∀ (s : SimpleSign), s⁻¹ = s := by decide
@[simp high] protected lemma div_eq_mul : ∀ (s s' : SimpleSign), s / s' = s * s' := by decide

lemma ne_one_iff : ∀ {s : SimpleSign}, s ≠ 1 ↔ s = -1 := by decide
lemma ne_neg_one_iff : ∀ {s : SimpleSign}, s ≠ -1 ↔ s = 1 := by decide

@[simp] lemma ne_neg : ∀ {s : SimpleSign}, s ≠ -s := by decide
@[simp] lemma neg_ne : ∀ {s : SimpleSign}, -s ≠ s := by decide

lemma eq_self_or_neg : ∀ (s s' : SimpleSign), s = s' ∨ s = -s' := by decide
lemma ne_iff_eq_neg : ∀ {s s' : SimpleSign}, ¬ s = s' ↔ s = -s' := by decide

instance : HasDistribNeg SimpleSign where
  neg_neg := by decide
  neg_mul := by decide
  mul_neg := by decide

instance : Nontrivial SimpleSign where
  exists_pair_ne := ⟨1, -1, by decide⟩

instance : LE SimpleSign where
  le a b := a = -1 ∨ b = 1

instance : LT SimpleSign where
  lt a b := a = -1 ∧ b = 1

@[inline] instance : DecidableLE SimpleSign := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))
@[inline] instance : DecidableLT SimpleSign := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

instance : LinearOrder SimpleSign where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_total := by decide
  lt_iff_le_not_ge := by decide
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  max a b := match a with
    | 1 => 1
    | -1 => b
  max_def := by decide
  min a b := match a with
    | -1 => -1
    | 1 => b
  min_def := by decide

instance : BoundedOrder SimpleSign where
  top := 1
  le_top := by decide
  bot := -1
  bot_le := by decide

@[simp] lemma le_one : ∀ (s : SimpleSign), s ≤ 1 := by decide
@[simp] lemma neg_one_le : ∀ (s : SimpleSign), -1 ≤ s := by decide
@[simp] lemma one_le_iff : ∀ {s : SimpleSign}, 1 ≤ s ↔ s = 1 := by decide
@[simp] lemma le_neg_one_iff : ∀ {s : SimpleSign}, s ≤ -1 ↔ s = -1 := by decide

@[simp] lemma bot_eq_neg_one : (⊥ : SimpleSign) = -1 := rfl
@[simp] lemma top_eq_one : (⊤ : SimpleSign) = 1 := rfl

@[simp] protected lemma le_neg_self_iff : ∀ {s : SimpleSign}, s ≤ -s ↔ s = -1 := by decide
@[simp] protected lemma neg_le_self_iff : ∀ {s : SimpleSign}, -s ≤ s ↔ s = 1 := by decide
@[simp] protected lemma neg_le_neg_iff : ∀ {s s' : SimpleSign}, -s ≤ -s' ↔ s' ≤ s := by decide
protected lemma neg_le_neg : ∀ {s s' : SimpleSign}, s ≤ s' → -s' ≤ -s := by decide

protected lemma max_neg_neg : ∀ (s s' : SimpleSign), max (-s) (-s') = -min s s' := by decide
protected lemma min_neg_neg : ∀ (s s' : SimpleSign), min (-s) (-s') = -max s s' := by decide

@[simp] lemma max_neg_self_left : ∀ (s : SimpleSign), max (-s) s = 1 := by decide
@[simp] lemma max_neg_self_right : ∀ (s : SimpleSign), max s (-s) = 1 := by decide
@[simp] lemma min_neg_self_left : ∀ (s : SimpleSign), min (-s) s = -1 := by decide
@[simp] lemma min_neg_self_right : ∀ (s : SimpleSign), min s (-s) = -1 := by decide

@[simp] lemma max_eq_one_iff : ∀ {s s' : SimpleSign}, max s s' = 1 ↔ s = 1 ∨ s' = 1 := by decide
@[simp] lemma max_eq_neg_one_iff : ∀ {s s' : SimpleSign}, max s s' = -1 ↔ s = -1 ∧ s' = -1 := by decide
@[simp] lemma min_eq_one_iff : ∀ {s s' : SimpleSign}, min s s' = 1 ↔ s = 1 ∧ s' = 1 := by decide
@[simp] lemma min_eq_neg_one_iff : ∀ {s s' : SimpleSign}, min s s' = -1 ↔ s = -1 ∨ s' = -1 := by decide

@[simp] lemma one_eq_max_iff : ∀ {s s' : SimpleSign}, 1 = max s s' ↔ s = 1 ∨ s' = 1 := by decide
@[simp] lemma neg_one_eq_max_iff : ∀ {s s' : SimpleSign}, -1 = max s s' ↔ s = -1 ∧ s' = -1 := by decide
@[simp] lemma one_eq_min_iff : ∀ {s s' : SimpleSign}, 1 = min s s' ↔ s = 1 ∧ s' = 1 := by decide
@[simp] lemma neg_one_eq_min_iff : ∀ {s s' : SimpleSign}, -1 = min s s' ↔ s = -1 ∨ s' = -1 := by decide

variable {α : Type*}

@[coe]
def coe [One α] [Neg α] : SimpleSign → α
  | 1 => 1
  | -1 => -1

instance {s : SimpleSign} [One α] [Neg α] : CoeDep SimpleSign s α where
  coe := s.coe

@[simp, norm_cast]
lemma coe_one [One α] [Neg α] : ((1 : SimpleSign) : α) = 1 := (rfl)

@[simp]
lemma coe_neg_one [One α] [Neg α] : ((-1 : SimpleSign) : α) = -1 := (rfl)

@[simp]
lemma coe_ne_zero [Zero α] [One α] [Neg α] [NeZero (1 : α)] [NeZero (-1 : α)]
    (s : SimpleSign) : (s : α) ≠ 0 := by
  cases s <;> simp [NeZero.ne]

@[simp]
lemma coe_mul_inj [MulOneClass α] [HasDistribNeg α] {s : SimpleSign} {x y : α} :
    s * x = s * y ↔ x = y := by cases s <;> simp

@[simp]
lemma mul_coe_inj [MulOneClass α] [HasDistribNeg α] {s : SimpleSign} {x y : α} :
    x * s = y * s ↔ x = y := by cases s <;> simp

@[simp]
lemma coe_signType_inj {s s' : SimpleSign} :
    (s : SignType) = s' ↔ s = s' := by decide +revert

@[grind inj]
lemma coe_signType_injective : Function.Injective ((↑) : SimpleSign → SignType) := by
  intro; decide +revert

@[simp, norm_cast]
lemma coe_neg [One α] [InvolutiveNeg α] (s : SimpleSign) :
    ((-s : SimpleSign) : α) = -s := by cases s <;> simp

@[simp, norm_cast]
lemma coe_mul [MulOneClass α] [HasDistribNeg α] (s s' : SimpleSign) :
    ((s * s' : SimpleSign) : α) = s * s' := by cases s <;> simp

@[simp]
lemma inv_coe [Group α] [HasDistribNeg α] (s : SimpleSign) :
    (s : α)⁻¹ = s := by cases s <;> simp

@[simp]
lemma abs_coe [Ring α] [LinearOrder α] [IsOrderedRing α] (s : SimpleSign) :
    |(s : α)| = 1 := by cases s <;> simp

@[simp]
lemma erealAbs_coe (s : SimpleSign) : (s : EReal).abs = 1 := by
  cases s <;> simp

@[simp]
lemma nnabs_coe (s : SimpleSign) : Real.nnabs s = 1 := by cases s <;> ext <;> simp

lemma coe_mul_eq_div [Group α] [HasDistribNeg α] (s s' : SimpleSign) :
    ((s * s' : SimpleSign) : α) = s / s' := by simp [div_eq_mul_inv]

lemma commute_coe_left [Monoid α] [HasDistribNeg α] (s : SimpleSign) (x : α) :
    Commute (s : α) x := by cases s <;> simp

lemma commute_coe_right [Monoid α] [HasDistribNeg α] (x : α) (s : SimpleSign) :
    Commute x (s : α) := by cases s <;> simp

@[simp, norm_cast]
lemma intCast_coe [AddGroupWithOne α] (s : SimpleSign) : ((s : ℤ) : α) = s := by
  cases s <;> simp

@[simp, norm_cast]
lemma realToEReal_coe (s : SimpleSign) : ((s : ℝ) : EReal) = s := by
  cases s <;> simp

@[simp]
lemma coe_mul_self [MulOneClass α] [HasDistribNeg α] (s : SimpleSign) :
    (s : α) * s = 1 := by
  rw [← SimpleSign.coe_mul, SimpleSign.mul_self, SimpleSign.coe_one]

@[simp]
lemma coe_mul_self_left [Monoid α] [HasDistribNeg α]
    (s : SimpleSign) (x : α) : s * (s * x) = x := by
  rw [← mul_assoc, coe_mul_self, one_mul]

@[simp]
lemma coe_mul_self_right [Monoid α] [HasDistribNeg α]
    (s : SimpleSign) (x : α) : x * s * s = x := by
  rw [mul_assoc, coe_mul_self, mul_one]

def ofValue [LinearOrder α] [Zero α] (x : α) (zeroSign : SimpleSign := 1) : SimpleSign :=
  match compare x 0 with
  | .lt => -1
  | .eq => zeroSign
  | .gt => 1

@[simp]
lemma ofValue_mul_abs [Ring α] [LinearOrder α] [IsOrderedRing α] (x : α) (zs : SimpleSign) :
    ofValue x zs * |x| = x := by
  rw [ofValue]
  split <;> rename_i hcmp
  · rw [compare_lt_iff_lt] at hcmp
    simp [abs_of_neg hcmp]
  · rw [compare_eq_iff_eq] at hcmp
    simp [hcmp]
  · rw [compare_gt_iff_gt] at hcmp
    simp [abs_of_pos hcmp]

@[simp]
lemma abs_mul_ofValue [Ring α] [LinearOrder α] [IsOrderedRing α] (x : α) (zs : SimpleSign) :
    |x| * ofValue x zs = x := by
  rw [commute_coe_right, ofValue_mul_abs]

@[simp]
lemma ofValue_zero [LinearOrder α] [Zero α] (zs : SimpleSign) : ofValue (0 : α) zs = zs := by
  simp [ofValue]

lemma ofValue_of_pos [LinearOrder α] [Zero α] {x : α} {zs : SimpleSign} (h : 0 < x) : ofValue x zs = 1 := by
  simp [ofValue, compare_gt_iff_gt.mpr h]

lemma ofValue_of_neg [LinearOrder α] [Zero α] {x : α} {zs : SimpleSign} (h : x < 0) : ofValue x zs = -1 := by
  simp [ofValue, compare_lt_iff_lt.mpr h]

lemma ofValue_of_nonneg [LinearOrder α] [Zero α] {x : α} (h : 0 ≤ x) : ofValue x 1 = 1 := by
  cases h.eq_or_lt
  · simp [← ‹0 = x›]
  · rw [ofValue_of_pos ‹_›]

lemma ofValue_of_nonpos [LinearOrder α] [Zero α] {x : α} (h : x ≤ 0) : ofValue x (-1) = -1 := by
  cases h.eq_or_lt
  · simp [‹x = 0›]
  · rw [ofValue_of_neg ‹_›]

@[simp]
lemma ofValue_eq_ofValue_iff [LinearOrder α] [Zero α]
    {x : α} {zs zs' : SimpleSign} :
    ofValue x zs = ofValue x zs' ↔ x = 0 → zs = zs' := by
  obtain h | rfl | h := lt_trichotomy x 0 <;>
    simp_all [ofValue_of_pos, ofValue_of_neg, ne_of_gt, ne_of_lt]

@[simp]
lemma ofValue_one_eq_one_iff [LinearOrder α] [Zero α] {x : α} :
    ofValue x 1 = 1 ↔ 0 ≤ x := by
  constructor
  · contrapose!
    intro hneg
    simp [ofValue_of_neg hneg]
  · exact ofValue_of_nonneg

@[simp]
lemma ofValue_neg_one_eq_one_iff [LinearOrder α] [Zero α] {x : α} :
    ofValue x (-1) = 1 ↔ 0 < x := by
  constructor
  · contrapose!
    intro hneg
    simp [ofValue_of_nonpos hneg]
  · exact ofValue_of_pos

@[simp]
lemma ofValue_one_eq_neg_one_iff [LinearOrder α] [Zero α] {x : α} :
    ofValue x 1 = -1 ↔ x < 0 := by
  constructor
  · contrapose!
    intro hpos
    simp [ofValue_of_nonneg hpos]
  · exact ofValue_of_neg

@[simp]
lemma ofValue_neg_one_eq_neg_one_iff [LinearOrder α] [Zero α] {x : α} :
    ofValue x (-1) = -1 ↔ x ≤ 0 := by
  constructor
  · contrapose!
    intro hpos
    simp [ofValue_of_pos hpos]
  · exact ofValue_of_nonpos

@[simp]
lemma ofValue_neg_neg [LinearOrder α] [AddCommGroup α] [IsOrderedAddMonoid α] {x : α} {s : SimpleSign} :
    ofValue (-x) (-s) = -ofValue x s := by
  obtain h | rfl | h := lt_trichotomy x 0 <;>
    simp [ofValue_of_neg, ofValue_of_pos, *]

@[simp]
lemma ofValue_signType_neg_neg {x : SignType} {s : SimpleSign} :
    ofValue (-x) (-s) = -ofValue x s := by
  obtain h | rfl | h := lt_trichotomy x 0 <;> simp_all [ofValue_of_neg, ofValue_of_pos]

@[simp]
lemma ofValue_ofValue [LinearOrder α] [Zero α]
    (x : α) (zs : SimpleSign) : ofValue x (ofValue x zs) = ofValue x zs := by
  obtain h | rfl | h := lt_trichotomy x 0 <;> simp_all [ofValue_of_pos, ofValue_of_neg]

@[simp]
lemma ofValue_coe [LinearOrder α] [Ring α] [IsStrictOrderedRing α]
    {s s' : SimpleSign} : ofValue (s : α) s' = s := by
  cases s <;> simp [ofValue_of_pos, ofValue_of_neg]

@[simp]
lemma ofValue_coe_signType {s s' : SimpleSign} : ofValue (s : SignType) s' = s := by
  cases s <;> simp [ofValue_of_pos, ofValue_of_neg]

@[simp]
lemma ofValue_coe_mul_eq_self_iff_nonneg [LinearOrder α] [Ring α] [IsStrictOrderedRing α]
    {s : SimpleSign} {x : α} : ofValue (s * x) s = s ↔ 0 ≤ x := by
  cases s <;> simp

alias ⟨_, ofValue_coe_mul_eq_self⟩ := ofValue_coe_mul_eq_self_iff_nonneg

@[norm_cast, simp]
lemma ofValue_signTypeCoe [LinearOrder α] [Ring α] [IsStrictOrderedRing α]
    (x : SignType) (zs : SimpleSign) : ofValue (x : α) zs = ofValue x zs := by
  obtain h | rfl | h := lt_trichotomy x 0 <;> simp_all [ofValue_of_pos, ofValue_of_neg]

@[norm_cast, simp]
lemma ofValue_intCast [LinearOrder α] [Ring α] [IsStrictOrderedRing α]
    (x : ℤ) (zs : SimpleSign) : ofValue (x : α) zs = ofValue x zs := by
  obtain h | rfl | h := lt_trichotomy x 0 <;> simp_all [ofValue_of_pos, ofValue_of_neg]

@[norm_cast, simp]
lemma ofValue_realToEReal (x : ℝ) (zs : SimpleSign) : ofValue (x : EReal) zs = ofValue x zs := by
  obtain h | rfl | h := lt_trichotomy x 0 <;> simp_all [ofValue_of_pos, ofValue_of_neg]

@[norm_cast, simp]
lemma ofValue_ennrealToEReal (x : ENNReal) (zs : SimpleSign) : ofValue (x : EReal) zs = ofValue x zs := by
  obtain h | rfl | h := lt_trichotomy x 0 <;> simp_all [ofValue_of_pos]

@[norm_cast, simp]
lemma ofValue_nnrealToReal [LinearOrder α] [Ring α] [IsStrictOrderedRing α]
    (x : NNReal) (zs : SimpleSign) : ofValue (x : ℝ) zs = ofValue x zs := by
  obtain h | rfl | h := lt_trichotomy x 0 <;> simp_all [ofValue_of_pos]

end LeanFloats.SimpleSign
