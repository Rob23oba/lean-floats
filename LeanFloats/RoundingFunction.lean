module
public import LeanFloats.SimpleSign
public import Mathlib.Tactic.Order
public import Mathlib.Tactic.Rify
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

@[simp]
lemma Int.fract_neg_eq_half_iff {α : Type*}
    [Field α] [LinearOrder α] [FloorRing α] [IsOrderedRing α] {x : α} :
    fract (-x) = 2⁻¹ ↔ fract x = 2⁻¹ := by
  grind [fract_neg, fract_neg_eq_zero]

namespace LeanFloats

structure RoundingFunction where
  toFun : ℝ → ℤ
  monotone_toFun : Monotone toFun
  toFun_intCast (x : ℤ) : toFun x = x

instance : FunLike RoundingFunction ℝ ℤ where
  coe := RoundingFunction.toFun
  coe_injective := by
    rintro ⟨a⟩ ⟨b⟩ h
    simpa using h

namespace RoundingFunction

@[ext]
protected lemma ext {f g : RoundingFunction} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

@[gcongr]
protected lemma monotone (f : RoundingFunction) : Monotone f := f.monotone_toFun

@[simp]
protected lemma apply_intCast (f : RoundingFunction) (x : ℤ) : f x = x := f.toFun_intCast x

@[simp]
protected lemma apply_natCast (f : RoundingFunction) (x : ℕ) : f x = x := by
  rw [← Int.cast_natCast, RoundingFunction.apply_intCast]

@[simp]
protected lemma apply_ofNat (f : RoundingFunction) (n : ℕ) : f ofNat(n) = ofNat(n) := by
  rw [← Lean.Grind.Semiring.natCast_eq_ofNat]
  exact RoundingFunction.apply_natCast f n

lemma apply_lt_add_one (f : RoundingFunction) (x : ℝ) : f x < x + 1 := by
  grw [Int.le_ceil x, f.apply_intCast]
  exact Int.ceil_lt_add_one x

lemma sub_one_lt_apply (f : RoundingFunction) (x : ℝ) : x - 1 < f x := by
  grw [← Int.floor_le x, f.apply_intCast]
  exact Int.sub_one_lt_floor x

lemma apply_eq_floor_or_ceil (f : RoundingFunction) (x : ℝ) : f x = ⌊x⌋ ∨ f x = ⌈x⌉ := by
  rw [eq_comm (a := f x), eq_comm (a := f x), Int.floor_eq_iff, Int.ceil_eq_iff]
  have := f.apply_lt_add_one x
  have := f.sub_one_lt_apply x
  grind

protected lemma apply_nonneg {f : RoundingFunction} {x : ℝ} (h : 0 ≤ x) : 0 ≤ f x := by
  simpa using f.monotone h

protected lemma apply_nonpos {f : RoundingFunction} {x : ℝ} (h : x ≤ 0) : f x ≤ 0 := by
  simpa using f.monotone h

open Mathlib.Meta.Positivity Qq in
@[positivity (_ : RoundingFunction) _]
meta def Base.valuePositivityExt : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℤ), ~q(($f : RoundingFunction) $x) => do
    match ← core q(inferInstance) (some q(inferInstance)) x with
    | .positive h =>
      assertInstancesCommute
      return .nonnegative q(($f).apply_nonneg ($h).le)
    | .nonnegative h =>
      assertInstancesCommute
      return .nonnegative q(($f).apply_nonneg $h)
    | _ => pure .none
  | _ => pure .none

lemma apply_le_of_le_natCast {f : RoundingFunction} {x : ℝ} {n : ℕ} (h : x ≤ n) : f x ≤ n := by
  grw [h, f.apply_natCast]

lemma apply_le_of_le_intCast {f : RoundingFunction} {x : ℝ} {n : ℤ} (h : x ≤ n) : f x ≤ n := by
  grw [h, f.apply_intCast]

lemma apply_ge_of_ge_natCast {f : RoundingFunction} {x : ℝ} {n : ℕ} (h : n ≤ x) : n ≤ f x := by
  grw [← h, f.apply_natCast]

lemma apply_ge_of_ge_intCast {f : RoundingFunction} {x : ℝ} {n : ℤ} (h : n ≤ x) : n ≤ f x := by
  grw [← h, f.apply_intCast]

lemma apply_le_ceil (f : RoundingFunction) (x : ℝ) : f x ≤ ⌈x⌉ := apply_le_of_le_intCast (Int.le_ceil x)
lemma floor_le_apply (f : RoundingFunction) (x : ℝ) : ⌊x⌋ ≤ f x := apply_ge_of_ge_intCast (Int.floor_le x)

lemma natAbs_le_of_abs_le {f : RoundingFunction} {x : ℝ} {n : ℕ} (h : |x| ≤ n) : (f x).natAbs ≤ n := by
  rw [abs_le] at h
  rw [← Nat.cast_le (α := ℤ), ← Int.abs_eq_natAbs, abs_le, neg_le]
  grw [← h.1, h.2, f.apply_natCast, ← Int.cast_natCast, ← Int.cast_neg, f.apply_intCast, neg_neg]
  trivial

class NegStable (f : RoundingFunction) where
  apply_neg (x : ℝ) : f (-x) = -f x

@[simp]
protected lemma apply_neg (f : RoundingFunction) [f.NegStable] (x : ℝ) : f (-x) = -f x :=
  NegStable.apply_neg x

protected lemma abs_apply (f : RoundingFunction) [f.NegStable] (x : ℝ) : |f x| = f |x| := by
  obtain h | h := le_total x 0
  · simp [abs_of_nonpos h, f.apply_neg, f.apply_nonpos h]
  · simp [abs_of_nonneg h, f.apply_nonneg h]

@[simp]
lemma apply_simpleSign_mul (f : RoundingFunction) [f.NegStable] (s : SimpleSign) (x : ℝ) :
    f (s * x) = s * f x := by cases s <;> simp

def opposite (f : RoundingFunction) : RoundingFunction where
  toFun x := -f (-x)
  monotone_toFun {a b} h := by dsimp; grw [h]
  toFun_intCast := by simp [← Int.cast_neg]

@[simp]
lemma opposite_apply (f : RoundingFunction) (x : ℝ) : f.opposite x = -f (-x) := rfl

@[simp]
lemma opposite_eq_self (f : RoundingFunction) [f.NegStable] : f.opposite = f := by
  ext x; simp

@[simp]
lemma opposite_opposite (f : RoundingFunction) : f.opposite.opposite = f := by
  ext x; simp

def flipOn (f : RoundingFunction) (s : SimpleSign) : RoundingFunction :=
  match s with
  | 1 => f
  | -1 => f.opposite

@[simp]
lemma flipOn_one (f : RoundingFunction) : f.flipOn 1 = f := (rfl)

@[simp]
lemma flipOn_neg_one (f : RoundingFunction) : f.flipOn (-1) = f.opposite := (rfl)

@[simp]
lemma flipOn_apply (f : RoundingFunction) (s : SimpleSign) (x : ℝ) :
    f.flipOn s x = s * f (s * x) := by cases s <;> simp

@[simp]
lemma flipOn_opposite (f : RoundingFunction) (s : SimpleSign) :
    f.opposite.flipOn s = f.flipOn (-s) := by cases s <;> simp

@[simp]
lemma opposite_flipOn (f : RoundingFunction) (s : SimpleSign) :
    (f.flipOn s).opposite = f.flipOn (-s) := by cases s <;> simp

@[simp]
lemma flipOn_eq_self (f : RoundingFunction) [f.NegStable] (s : SimpleSign) :
    f.flipOn s = f := by cases s <;> simp

@[simp]
lemma flipOn_flipOn (f : RoundingFunction) (s s' : SimpleSign) :
    (f.flipOn s).flipOn s' = f.flipOn (s * s') := by
  ext; simp [← mul_assoc, mul_comm]

instance {f : RoundingFunction} [f.NegStable] : f.opposite.NegStable where
  apply_neg := by simp

noncomputable def balanced (f : RoundingFunction) : RoundingFunction where
  toFun x := if 0 ≤ x then f x else -f (-x)
  monotone_toFun {a b} h := by
    dsimp only
    split <;> split
    · grw [h]
    · order
    · grw [le_of_not_ge ‹¬0 ≤ a›, ← ‹0 ≤ b›]; simp
    · grw [h]
  toFun_intCast := by simp [← Int.cast_neg]

lemma balanced_apply (f : RoundingFunction) (x : ℝ) :
    f.balanced x = if 0 ≤ x then f x else -f (-x) := rfl

lemma balanced_apply_of_nonneg {f : RoundingFunction} {x : ℝ} (h : 0 ≤ x) :
    f.balanced x = f x := by simp [balanced_apply, h]

lemma balanced_apply_of_nonpos {f : RoundingFunction} {x : ℝ} (h : x ≤ 0) :
    f.balanced x = -f (-x) := by simp +contextual [balanced_apply, le_antisymm h]

lemma balanced_eq_self (f : RoundingFunction) [f.NegStable] :
    f.balanced = f := by ext; simp [balanced_apply]

instance {f : RoundingFunction} : f.balanced.NegStable where
  apply_neg x := by
    obtain h | h := le_total x 0 <;> simp [balanced_apply_of_nonneg, balanced_apply_of_nonpos, h]

class IsNearest (f : RoundingFunction) where
  toFun_le (x : ℝ) : f x ≤ x + 2⁻¹
  toFun_ge (x : ℝ) : x - 2⁻¹ ≤ f x

lemma apply_lt_add_half (f : RoundingFunction) [f.IsNearest] (x : ℝ) : f x ≤ x + 2⁻¹ := IsNearest.toFun_le x
lemma sub_half_lt_apply (f : RoundingFunction) [f.IsNearest] (x : ℝ) : x - 2⁻¹ ≤ f x := IsNearest.toFun_ge x

lemma apply_intCast_add_of_abs_lt {f : RoundingFunction} {y : ℝ} [f.IsNearest]
    {x : ℤ} (hy : |y| < 2⁻¹) : f (x + y) = x := by
  have := f.apply_lt_add_half (x + y)
  have := f.sub_half_lt_apply (x + y)
  apply le_antisymm <;> rw [← Int.sub_one_lt_iff] <;> rify <;> grind

lemma apply_intCast_sub_of_abs_lt {f : RoundingFunction} {y : ℝ} [f.IsNearest]
    {x : ℤ} (hy : |y| < 2⁻¹) : f (x - y) = x := by
  simpa [sub_eq_add_neg] using apply_intCast_add_of_abs_lt (y := -y) (by simpa using hy)

lemma apply_natCast_add_of_abs_lt {f : RoundingFunction} {y : ℝ} [f.IsNearest]
    {x : ℕ} (hy : |y| < 2⁻¹) : f (x + y) = x := by
  simpa using apply_intCast_add_of_abs_lt (x := x) hy

lemma apply_natCast_sub_of_abs_lt {f : RoundingFunction} {y : ℝ} [f.IsNearest]
    {x : ℕ} (hy : |y| < 2⁻¹) : f (x - y) = x := by
  simpa using apply_intCast_sub_of_abs_lt (x := x) hy

instance {f : RoundingFunction} [f.IsNearest] : f.opposite.IsNearest where
  toFun_le x := by simp; grind [IsNearest.toFun_ge]
  toFun_ge x := by simp; grind [IsNearest.toFun_le]

instance {f : RoundingFunction} [f.IsNearest] : f.balanced.IsNearest where
  toFun_le x := by simp [balanced_apply]; grind [IsNearest.toFun_le, IsNearest.toFun_ge]
  toFun_ge x := by simp [balanced_apply]; grind [IsNearest.toFun_le, IsNearest.toFun_ge]

def ofNearest (f : ℝ → ℤ) (hle : ∀ x, f x ≤ x + 2⁻¹) (hge : ∀ x, x - 2⁻¹ ≤ f x) :
    RoundingFunction where
  toFun := f
  monotone_toFun {a b} h := by
    rw [← Int.sub_one_lt_iff]
    rify; grind
  toFun_intCast x := by
    apply le_antisymm <;> simp [Int.le_iff_lt_add_one, ← Int.cast_lt (R := ℝ)] <;> grind

@[simp]
lemma coe_ofNearest (f hle hge) : ofNearest f hle hge = f := rfl

instance (f hle hge) : (ofNearest f hle hge).IsNearest where
  toFun_le x := by simp [hle]
  toFun_ge x := by simp [hge]

protected noncomputable def floor : RoundingFunction where
  toFun x := ⌊x⌋
  monotone_toFun := Int.floor_mono
  toFun_intCast := Int.floor_intCast

protected noncomputable def ceil : RoundingFunction where
  toFun x := ⌈x⌉
  monotone_toFun := Int.ceil_mono
  toFun_intCast := Int.ceil_intCast

noncomputable abbrev towardsZero : RoundingFunction :=
  balanced .floor

noncomputable def tiesToInfinity : RoundingFunction :=
  .ofNearest round (fun x => by simpa using round_le_add_half x)
    (fun x => by simpa using (sub_half_lt_round x).le)
deriving IsNearest

noncomputable abbrev tiesAway : RoundingFunction :=
  balanced tiesToInfinity

noncomputable def tiesToEven : RoundingFunction :=
  .ofNearest (fun x => if Int.fract x = 2⁻¹ then (⌊x⌋ + 1) / 2 * 2 else round x) ?le ?ge
where finally
  · intro x
    rw [Int.fract]
    split
    · conv => rhs; rw [eq_add_of_sub_eq ‹x - _ = _›]
      grw [Int.ediv_mul_self, Int.cast_sub, sub_le_self _ (by simp [Int.emod_nonneg])]
      grind
    · simpa using round_le_add_half x
  · intro x
    rw [Int.fract]
    split
    · conv => rhs; rw [eq_add_of_sub_eq ‹x - _ = _›]
      grw [Int.ediv_mul_self, Int.cast_sub,
        Int.le_sub_one_iff.mpr <| Int.emod_lt_of_pos _ (by decide)]
      grind
    · simpa using (sub_half_lt_round x).le
deriving IsNearest

@[simp]
lemma floor_apply (x : ℝ) : RoundingFunction.floor x = ⌊x⌋ := rfl

@[simp]
lemma ceil_apply (x : ℝ) : RoundingFunction.ceil x = ⌈x⌉ := rfl

@[simp]
lemma tiesToInfinity_eq_round (x : ℝ) : tiesToInfinity x = round x := rfl

lemma tiesToEven_intCast_add_of_even {x : ℤ} {y : ℝ} (hx : Even x) (hy : |y| ≤ 2⁻¹) :
    tiesToEven (x + y) = x := by
  by_cases heq : |y| = 2⁻¹
  · rw [abs_eq (by simp)] at heq
    obtain rfl | rfl := heq
    · norm_num [tiesToEven]
      grind
    · norm_num [tiesToEven]
      grind
  · exact apply_intCast_add_of_abs_lt (by grind)

lemma tiesToEven_intCast_sub_of_even {x : ℤ} {y : ℝ} (hx : Even x) (hy : |y| ≤ 2⁻¹) :
    tiesToEven (x - y) = x := by
  simpa [sub_eq_add_neg] using tiesToEven_intCast_add_of_even (y := -y) hx (by simpa using hy)

lemma tiesToEven_natCast_add_of_even {x : ℕ} {y : ℝ} (hx : Even x) (hy : |y| ≤ 2⁻¹) :
    tiesToEven (x + y) = x := by
  simpa using tiesToEven_intCast_add_of_even (x := x) (mod_cast hx) hy

lemma tiesToEven_natCast_sub_of_even {x : ℕ} {y : ℝ} (hx : Even x) (hy : |y| ≤ 2⁻¹) :
    tiesToEven (x - y) = x := by
  simpa using tiesToEven_intCast_sub_of_even (x := x) (mod_cast hx) hy

theorem tiesToEven_cases {motive : ℝ → ℤ → Prop}
    (even : ∀ n : ℤ, ∀ x : ℝ, Even n → |x| ≤ 2⁻¹ → motive (n + x) n)
    (odd : ∀ n : ℤ, ∀ x : ℝ, Odd n → |x| < 2⁻¹ → motive (n + x) n)
    (x : ℝ) : motive x (tiesToEven x) := by
  have : ∃ (n : ℤ) (y : ℝ), x = n + y ∧ 0 ≤ y ∧ y < 1 :=
    ⟨⌊x⌋, Int.fract x, (Int.floor_add_fract x).symm, Int.fract_nonneg x, Int.fract_lt_one x⟩
  obtain ⟨n, x, rfl, hx₁, hx₂⟩ := this
  obtain h | rfl | h := lt_trichotomy x 2⁻¹
  · rw [apply_intCast_add_of_abs_lt (by grind)]
    grind [n.even_or_odd]
  · obtain h' | h' := n.even_or_odd
    · rw [tiesToEven_intCast_add_of_even h' (by simp)]
      grind
    · have : (n + 2⁻¹ : ℝ) = (n + 1 : ℤ) - 2⁻¹ := by grind
      rw [this, tiesToEven_intCast_sub_of_even (by simp_all) (by simp)]
      apply even <;> simp_all
  · have : (n + x : ℝ) = (n + 1 : ℤ) + (x - 1) := by grind
    rw [this, apply_intCast_add_of_abs_lt (by grind)]
    obtain h' | h' := (n + 1).even_or_odd
    · apply even <;> grind
    · apply odd <;> grind

instance : NegStable tiesToEven where
  apply_neg x := by
    induction x using tiesToEven_cases with
    | even n x hn hx =>
      rw [neg_add, ← Int.cast_neg, tiesToEven_intCast_add_of_even (by simpa) (by simpa)]
    | odd n x hn hx =>
      rw [neg_add, ← Int.cast_neg, apply_intCast_add_of_abs_lt (by simpa)]

@[simp]
lemma opposite_floor : RoundingFunction.floor.opposite = .ceil := by
  ext x; simp [Int.floor_neg]

@[simp]
lemma opposite_ceil : RoundingFunction.ceil.opposite = .floor := by
  ext x; simp [Int.ceil_neg]

def RepelsAtInfinity (f : RoundingFunction) (s : SimpleSign) : Prop :=
  match s with
  | 1 => ∀ᶠ x in Filter.atTop, f x = ⌊x⌋
  | -1 => ∀ᶠ x in Filter.atBot, f x = ⌈x⌉

noncomputable instance : Decidable (RepelsAtInfinity f s) :=
  Classical.propDecidable _

@[simp]
lemma repelsAtInfinity_opposite_iff {f : RoundingFunction} {s : SimpleSign} :
    f.opposite.RepelsAtInfinity s ↔ f.RepelsAtInfinity (-s) := by
  wlog hs : s = 1
  · cases s.ne_one_iff.mp hs
    simp [← this]
  simp only [hs, RepelsAtInfinity, RoundingFunction.opposite_apply, Filter.eventually_atTop,
    Filter.eventually_atBot]
  conv =>
    rw [← (Equiv.neg ℝ).exists_congr (fun _ => Iff.rfl)]
    enter [1, 1, a]; rw [← (Equiv.neg ℝ).forall_congr (fun _ => Iff.rfl)]
  simp [Int.floor_neg]

lemma repelsAtInfinity_iff_repelsAtInfinity_one
    {f : RoundingFunction} {s : SimpleSign} [f.NegStable] :
    f.RepelsAtInfinity s ↔ f.RepelsAtInfinity 1 := by
  cases s <;> simp [← repelsAtInfinity_opposite_iff]

@[simp]
lemma repelsAtInfinity_balanced_iff {f : RoundingFunction} {s : SimpleSign} :
    f.balanced.RepelsAtInfinity s ↔ f.RepelsAtInfinity 1 := by
  wlog hs : s = 1
  · cases s.ne_one_iff.mp hs
    rw [← repelsAtInfinity_opposite_iff, opposite_eq_self, this rfl]
  subst hs
  simp only [RepelsAtInfinity]
  apply Filter.eventually_congr
  simp only [Filter.eventually_atTop]
  use 0
  simp +contextual [f.balanced_apply_of_nonneg]

@[simp]
lemma not_repelsAtInfinity {f : RoundingFunction} [f.IsNearest] {s : SimpleSign} :
    ¬f.RepelsAtInfinity s := by
  wlog hs : s = 1
  · simpa [s.ne_one_iff.mp hs] using @this f.opposite _ 1 rfl
  subst hs
  simp only [RepelsAtInfinity, Filter.eventually_atTop]
  intro ⟨a, ha⟩
  specialize ha ((⌈a⌉ + 1 : ℤ) - 1/4) (by grind [Int.le_ceil])
  rw [apply_intCast_sub_of_abs_lt (by norm_num)] at ha
  norm_num [add_sub_assoc] at ha

@[simp]
lemma repelsAtInfinity_floor_iff {s : SimpleSign} :
    RoundingFunction.floor.RepelsAtInfinity s ↔ s = 1 := by
  cases s
  · simp [RepelsAtInfinity]
  · simp only [RepelsAtInfinity, floor_apply, Filter.eventually_atBot, reduceCtorEq, iff_false]
    intro ⟨a, ha⟩
    specialize ha (⌊a⌋ - 1/2) (by grind [Int.floor_le])
    norm_num [sub_eq_add_neg] at ha

@[simp]
lemma repelsAtInfinity_ceil_iff {s : SimpleSign} :
    RoundingFunction.ceil.RepelsAtInfinity s ↔ s = -1 := by
  rw [← opposite_floor, repelsAtInfinity_opposite_iff,
    repelsAtInfinity_floor_iff, neg_eq_iff_eq_neg]

example : towardsZero.RepelsAtInfinity s := by simp
example : ¬tiesToEven.RepelsAtInfinity s := by simp
example : ¬tiesAway.RepelsAtInfinity s := by simp

end LeanFloats.RoundingFunction
