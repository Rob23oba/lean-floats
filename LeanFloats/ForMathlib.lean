module
public import Mathlib.Data.EReal.Inv
public import Mathlib.Data.Sign.Defs
public import Mathlib.Data.Int.Log
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.NNReal.Basic

public section

@[simp] lemma Real.nnabs_neg (x : ℝ) : (-x).nnabs = x.nnabs := by ext; simp

@[to_dual eq_iff_eq_zero_of_nonpos_of_nonneg]
lemma eq_iff_eq_zero_of_nonneg_of_nonpos [PartialOrder α] [Zero α] {a b : α} (ha : 0 ≤ a) (hb : b ≤ 0) :
    a = b ↔ a = 0 ∧ b = 0 := by grind

@[simp]
lemma ENNReal.toEReal_nonneg (x : ENNReal) : 0 ≤ x.toEReal := by
  cases x <;> norm_cast; simp

instance [SubtractionMonoid α] {x : α} [NeZero x] : NeZero (-x) where
  out := by simp [NeZero.ne]

instance {x : SignType} [NeZero x] : NeZero (-x) where
  out := by simp [NeZero.ne]

instance {x : EReal} [NeZero x] : NeZero (-x) where
  out := by simp [NeZero.ne]

lemma Int.toNat_neg_eq_natAbs {x : ℤ} (h : x ≤ 0) : (-x).toNat = x.natAbs := by lia
lemma Int.toNat_eq_natAbs {x : ℤ} (h : 0 ≤ x) : x.toNat = x.natAbs := by lia

@[simp]
lemma Real.nnabs_intCast (x : ℤ) : (x : Real).nnabs = (x.natAbs : NNReal) := by
  ext; simp

@[simp]
theorem Int.floor_div_ofNat
    {k : Type*} [Field k] [LinearOrder k] [IsOrderedRing k] [FloorRing k]
    (a : k) (n : ℕ) [n.AtLeastTwo] : ⌊a / ofNat(n)⌋ = ⌊a⌋ / ofNat(n) := by
  rw [← Nat.cast_ofNat, Int.floor_div_natCast, Nat.cast_ofNat]

theorem Int.fract_fract_mul
    {k : Type*} [Ring k] [LinearOrder k] [IsOrderedRing k] [FloorRing k]
    (a : k) (n : ℕ) : Int.fract (Int.fract a * n) = Int.fract (a * n) := by
  unfold Int.fract
  rw [sub_mul]
  norm_cast
  rw [floor_sub_intCast]
  simp

@[simp]
theorem Int.fract_ofNat_mul_natCast_add
    {k : Type*} [Ring k] [LinearOrder k] [IsOrderedRing k] [FloorRing k]
    (n m : ℕ) [n.AtLeastTwo] (a : k) :
    Int.fract (ofNat(n) * m + a) = Int.fract a := by
  rw [← Nat.cast_ofNat, ← Nat.cast_mul, Int.fract_natCast_add]

@[simp]
theorem Int.fract_natCast_mul_ofNat_add
    {k : Type*} [Ring k] [LinearOrder k] [IsOrderedRing k] [FloorRing k]
    (n m : ℕ) [m.AtLeastTwo] (a : k) :
    Int.fract (n * ofNat(m) + a) = Int.fract a := by
  rw [← Nat.cast_ofNat, ← Nat.cast_mul, Int.fract_natCast_add]

@[simp]
theorem Int.fract_ofNat_mul_intCast_add
    {k : Type*} [Ring k] [LinearOrder k] [IsOrderedRing k] [FloorRing k]
    (n : ℤ) (m : ℕ) [m.AtLeastTwo] (a : k) :
    Int.fract (ofNat(m) * n + a) = Int.fract a := by
  rw [← Int.cast_ofNat, ← Int.cast_mul, Int.fract_intCast_add]

@[simp]
theorem Int.fract_intCast_mul_ofNat_add
    {k : Type*} [Ring k] [LinearOrder k] [IsOrderedRing k] [FloorRing k]
    (n : ℤ) (m : ℕ) [m.AtLeastTwo] (a : k) :
    Int.fract (n * ofNat(m) + a) = Int.fract a := by
  rw [← Int.cast_ofNat, ← Int.cast_mul, Int.fract_intCast_add]

theorem Int.floor_natCast_mul_zpow_of_nonneg
    {k k' : Type*} [Field k] [LinearOrder k] [IsOrderedRing k] [FloorRing k]
    [Field k'] [CharZero k'] (n : ℕ) (m : ℤ) (hm : 0 ≤ m) :
    ⌊(n * 2 ^ m : k)⌋ = (n * 2 ^ m : k') := by
  rw [← Int.toNat_of_nonneg hm]
  norm_cast
  rw [Int.floor_natCast]

theorem Int.log_eq_iff {R : Type*} [Semifield R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorSemiring R] {b : ℕ} {a : R} {z : ℤ}
    (hb : 1 < b) (ha : 0 < a) :
    Int.log b a = z ↔ b ^ z ≤ a ∧ a < b ^ (z + 1) := by
  constructor
  · rintro rfl
    simp [Int.zpow_log_le_self hb ha, Int.lt_zpow_succ_log_self hb]
  · rintro ⟨h₁, h₂⟩
    apply le_antisymm
    · rwa [Int.le_iff_lt_add_one, ← Int.lt_zpow_iff_log_lt hb ha]
    · rwa [← Int.zpow_le_iff_le_log hb ha]

@[simp]
theorem Int.log_mul_zpow {R : Type*} [Semifield R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorSemiring R] {b : ℕ} {a : R} (hb : 1 < b) (ha : 0 < a)
    (z : ℤ) : Int.log b (a * b ^ z) = Int.log b a + z := by
  have hbpos : 0 < b := by positivity
  rw [log_eq_iff hb (mul_pos ha (zpow_pos (by positivity) _)), zpow_add₀ (by simp [hbpos.ne'])]
  simp only [Nat.cast_pos, hbpos, zpow_pos, mul_le_mul_iff_left₀, ne_eq, Nat.cast_eq_zero,
    hbpos.ne', not_false_eq_true, zpow_add₀, zpow_one, mul_right_comm, mul_lt_mul_iff_left₀]
  rw [← zpow_add_one₀ (by positivity), ← Int.log_eq_iff hb ha]

@[simp]
theorem Int.log_mul_ofNat_zpow {R : Type*} [Semifield R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorSemiring R] {b : ℕ} [b.AtLeastTwo] {a : R} (ha : 0 < a)
    (z : ℤ) : Int.log ofNat(b) (a * ofNat(b) ^ z) = Int.log ofNat(b) a + z := by
  apply Int.log_mul_zpow <;> simp_all

@[simp]
theorem Int.log_div_zpow {R : Type*} [Semifield R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorSemiring R] {b : ℕ} {a : R} (hb : 1 < b) (ha : 0 < a)
    (z : ℤ) : Int.log b (a / b ^ z) = Int.log b a - z := by
  rw [div_eq_mul_inv, ← zpow_neg, log_mul_zpow hb ha, sub_eq_add_neg]

@[simp]
theorem Int.log_div_ofNat_zpow {R : Type*} [Semifield R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorSemiring R] {b : ℕ} [b.AtLeastTwo] {a : R} (ha : 0 < a)
    (z : ℤ) : Int.log ofNat(b) (a / ofNat(b) ^ z) = Int.log ofNat(b) a - z := by
  apply Int.log_div_zpow <;> simp_all

theorem Int.log_natCast_add_eq_natLog {R : Type*} [Semifield R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorSemiring R] {b a : ℕ} {f : R} (ha : 0 < a)
    (hf₁ : 0 ≤ f) (hf₂ : f < 1) :
    Int.log b (a + f) = Nat.log b a := by
  by_cases! hb : b ≤ 1
  · match b with
    | 0 | 1 => simp_all
  rw [log_eq_iff hb (by positivity)]
  constructor
  · grw [← hf₁, add_zero]
    norm_cast
    exact b.pow_log_le_self ha.ne'
  · grw [hf₂]
    norm_cast
    rw [Nat.add_one_le_iff]
    exact Nat.lt_pow_succ_log_self hb a

@[simp]
theorem Nat.log2_one : (1 : Nat).log2 = 0 := rfl

@[simp]
theorem Nat.log2_shiftLeft {n m : Nat} (hn : n ≠ 0) :
    (n <<< m).log2 = n.log2 + m := by
  induction m with
  | zero => simp
  | succ k ih => simp [Nat.shiftLeft_succ, Nat.log2_two_mul, hn, ih, add_assoc]

@[simp]
theorem Nat.log2_div_two (n : Nat) :
    (n / 2).log2 = n.log2 - 1 := by
  by_cases! h : n < 2
  · match n with | 0 | 1 => simp_all
  · rw [Nat.log2_eq_iff (by lia)]
    have hne : n ≠ 0 := by lia
    have : 1 ≤ n.log2 := by simpa [Nat.le_log2 hne]
    rw [Nat.pow_sub_one (by decide) (by lia)]
    constructor
    · exact Nat.div_le_div_right (Nat.log2_self_le hne)
    · simp [this, div_lt_iff_lt_mul, ← Nat.pow_succ, Nat.lt_log2_self]

@[simp]
theorem Nat.log2_shiftRight (n m : Nat) :
    (n >>> m).log2 = n.log2 - m := by
  induction m with
  | zero => simp
  | succ k ih => simp [Nat.shiftRight_succ, ih, Nat.sub_sub]

@[simp]
theorem Nat.log2_div_two_pow (n m : Nat) :
    (n / 2 ^ m).log2 = n.log2 - m := by
  simp [← Nat.shiftRight_eq_div_pow]

theorem BitVec.log2_toNat_lt {w : Nat} (x : BitVec w) (h : w ≠ 0) : x.toNat.log2 < w := by
  by_cases hx : x.toNat = 0
  · simp_all [h.pos]
  · simp [Nat.log2_lt hx, x.isLt]

theorem Nat.bit_add_bit {b c : Bool} {m n : Nat} :
    Nat.bit b m + Nat.bit c n = Nat.bit (b ^^ c) (m + n + (b && c).toNat) := by
  cases b <;> cases c <;> simp +arith

theorem Nat.and_add_or_eq (a b : Nat) :
    (a &&& b) + (a ||| b) = a + b := by
  induction a using Nat.binaryRec generalizing b with
  | zero => simp
  | bit b₁ n₁ ih =>
    induction b using Nat.binaryRec with
    | zero => simp
    | bit b₂ n₂ =>
      simp only [land_bit, lor_bit, bit_add_bit, ih]
      congr 1
      · clear *-b₁ b₂
        decide +revert
      · congr 1
        clear *-b₁ b₂
        decide +revert

theorem Nat.or_eq_add_of_and_eq_zero {a b : Nat} (h : a &&& b = 0) :
    a ||| b = a + b := by
  rw [← Nat.and_add_or_eq, h, Nat.zero_add]

theorem BitVec.toNat_append_eq_add {w w' : Nat} (x : BitVec w) (y : BitVec w') :
    (x ++ y).toNat = x.toNat * 2 ^ w' + y.toNat := by
  rw [toNat_append, Nat.shiftLeft_eq]
  apply Nat.or_eq_add_of_and_eq_zero
  apply Nat.eq_of_testBit_eq
  simp +contextual [Nat.testBit_mul_two_pow, ← BitVec.getLsbD.eq_def, BitVec.getLsbD_of_ge]

theorem Nat.log2_two_pow_add {n m : ℕ} (h : m < 2 ^ n) :
    (2 ^ n + m).log2 = n := by
  rw [Nat.log2_eq_iff (by positivity)]
  grw [h]
  simp [Nat.two_pow_succ]

@[gcongr]
theorem Nat.log2_mono {n m : ℕ} (h : n ≤ m) : Nat.log2 n ≤ Nat.log2 m := by
  simp only [Nat.log2_eq_log_two]
  grw [h]

theorem Nat.log_add_log_le_log_mul {b n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    log b n + log b m ≤ log b (n * m) := by
  by_cases! hb : b ≤ 1
  · simp [hb, Nat.log_of_left_le_one]
  simp only [ne_eq, _root_.mul_eq_zero, hn, hm, or_self, not_false_eq_true, le_log_iff_pow_le, Nat.pow_add, hb]
  exact Nat.mul_le_mul (pow_log_le_self b hn) (pow_log_le_self b hm)

theorem Nat.log2_add_log2_le_log2_mul {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    log2 n + log2 m ≤ log2 (n * m) := by
  simp [Nat.log2_eq_log_two, Nat.log_add_log_le_log_mul, *]

theorem Nat.log_mul_le (b n m : ℕ) : log b (n * m) ≤ log b n + log b m + 1 := by
  by_cases! hb : b ≤ 1
  · simp [hb, Nat.log_of_left_le_one]
  by_cases! hn : n = 0
  · simp [hn]
  by_cases! hm : m = 0
  · simp [hm]
  rw [Nat.le_iff_lt_add_one]
  rw [Nat.log_lt_iff_lt_pow hb (by simp [*])]
  grw [lt_pow_succ_log_self hb n, lt_pow_succ_log_self hb m]
  simp [← pow_add, add_assoc, add_left_comm]

theorem Nat.log2_mul_le (n m : ℕ) : (n * m).log2 ≤ n.log2 + m.log2 + 1 := by
  simp [Nat.log2_eq_log_two, Nat.log_mul_le, *]

theorem Nat.log_div_le (b n m : ℕ) : log b (n / m) ≤ log b n - log b m := by
  by_cases! hb : b ≤ 1
  · simp [hb, Nat.log_of_left_le_one]
  by_cases! hm : m = 0
  · simp [hm]
  by_cases! hnm : n < m
  · simp [Nat.div_eq_of_lt hnm]
  have : n / m ≠ 0 := by simp [*]
  simp only [Nat.le_iff_lt_add_one, Nat.log_lt_iff_lt_pow hb this, div_lt_iff_lt_mul hm.pos]
  grw [lt_pow_succ_log_self hb n, ← pow_log_le_self b hm]
  rw [← Nat.pow_add]
  apply Nat.pow_le_pow_right hb.pos
  lia

theorem Nat.log2_div_le (n m : ℕ) : log2 (n / m) ≤ log2 n - log2 m := by
  simp [Nat.log2_eq_log_two, Nat.log_div_le]

theorem Nat.log_sub_log_le_log_div_add_one {b n m : ℕ} (hm : m ≠ 0) :
    log b n - log b m ≤ log b (n / m) + 1 := by
  by_cases! hb : b ≤ 1
  · simp [hb, Nat.log_of_left_le_one]
  by_cases! hn : n = 0
  · simp [hn]
  by_cases! hnm : n < m
  · grw [hnm]
    simp
  have : n / m ≠ 0 := by simp [*]
  grw [← pow_log_le_self b hn, lt_pow_succ_log_self hb m]
  simp [Nat.log_div_base_pow, hb]; lia

theorem Nat.log2_sub_log2_le_log2_div_add_one {m : ℕ} (hm : m ≠ 0) (n : ℕ) :
    n.log2 - m.log2 ≤ (n / m).log2 + 1 := by
  simpa [Nat.log2_eq_log_two] using Nat.log_sub_log_le_log_div_add_one hm

@[simp]
theorem Nat.log_sqrt (b n : ℕ) : log b n.sqrt = log b n / 2 := by
  by_cases! hb : b ≤ 1
  · simp [hb, Nat.log_of_left_le_one]
  by_cases hn : n = 0
  · simp [hn]
  rw [Nat.log_eq_iff (by simp [Nat.sqrt_eq_zero, *])]
  constructor
  · rw [Nat.le_sqrt, ← Nat.pow_add]
    grw [← mul_two, Nat.div_mul_le_self, Nat.pow_log_le_self b hn]
    exact hb.le
  · rw [Nat.sqrt_lt, ← Nat.pow_add]
    grw [lt_pow_succ_log_self hb n]
    apply Nat.pow_le_pow_right hb.pos
    lia

@[simp]
theorem Nat.log2_sqrt (n : ℕ) : n.sqrt.log2 = n.log2 / 2 := by
  simp [Nat.log2_eq_log_two, Nat.log_sqrt]

@[simp]
theorem Int.ediv_eq (a b : ℤ) : a.ediv b = a / b := by rfl

theorem pow_toNat_eq_zpow {G : Type*} [DivInvMonoid G]
    {z : ℤ} (h : 0 ≤ z) (x : G) : x ^ z.toNat = x ^ z := by
  simp [← zpow_natCast, h]

@[simp]
theorem EReal.toReal_abs (x : EReal) : x.abs.toReal = |x.toReal| := by
  cases x <;> simp [EReal.abs_def]

@[simp]
theorem ENNReal.abs_toEReal (x : ENNReal) : (x.toEReal : EReal).abs = x := by
  cases x <;> simp [EReal.coe_nnreal_eq_coe_real, EReal.abs_def]

@[simp]
theorem EReal.abs_natCast (n : Nat) : (n : EReal).abs = n := by
  rw [← EReal.coe_natCast, EReal.abs_def]
  simp

@[simp]
theorem EReal.abs_one : (1 : EReal).abs = 1 := by
  rw [← Nat.cast_one, EReal.abs_natCast, Nat.cast_one]

@[simp]
theorem EReal.abs_ofNat {n : Nat} [n.AtLeastTwo] : (ofNat(n) : EReal).abs = ofNat(n) := by
  rw [← Nat.cast_ofNat, EReal.abs_natCast, Nat.cast_ofNat]

attribute [simp] zpow_ne_zero zpow_pos zpow_nonneg

instance {α : Type*} [LinearOrder α] : Std.LawfulOrderOrd α where
  isLE_compare a b := by
    rw [LinearOrder.compare_eq_compareOfLessAndEq, isLE_compareOfLessAndEq le_antisymm not_le le_total]
  isGE_compare a b := by
    rw [LinearOrder.compare_eq_compareOfLessAndEq, isGE_compareOfLessAndEq le_antisymm not_le le_total]

@[grind =]
lemma compare_eq_ite {α : Type*} [LE α] [DecidableLE α] [Ord α] [Std.LawfulOrderOrd α] {a b : α} :
    compare a b = if a ≤ b then if b ≤ a then .eq else .lt else .gt := by
  simp only [← Std.isLE_compare (a := a), ← Std.isGE_compare (a := a)]
  generalize compare a b = o
  decide +revert

attribute [grind =] Ordering.isLE Ordering.isGE Ordering.swap

attribute [gcongr low] abs_le_abs_of_nonpos

lemma compare_eq_compare_of_le {α β : Type*} {a b : α} {c d : β} [LE α] [LE β] [Ord α] [Ord β]
    [Std.LawfulOrderOrd α] [Std.LawfulOrderOrd β] (h₁ : a ≤ b ↔ c ≤ d) (h₂ : b ≤ a ↔ d ≤ c) :
    compare a b = compare c d := by
  classical simp [compare_eq_ite, h₁, h₂]

@[simp]
lemma compare_add_left {α : Type*} [LinearOrder α] [Semiring α] [IsStrictOrderedRing α]
    {a b c : α} : compare (c + a) (c + b) = compare a b :=
  compare_eq_compare_of_le (add_le_add_iff_left c) (add_le_add_iff_left c)

@[simp]
lemma compare_add_right {α : Type*} [LinearOrder α] [Semiring α] [IsStrictOrderedRing α]
    {a b c : α} : compare (a + c) (b + c) = compare a b :=
  compare_eq_compare_of_le (add_le_add_iff_right c) (add_le_add_iff_right c)

@[simp]
lemma compare_neg {α : Type*} [LinearOrder α] [Ring α] [IsStrictOrderedRing α] {a b : α} :
    compare (-a) (-b) = compare b a :=
  compare_eq_compare_of_le neg_le_neg_iff neg_le_neg_iff

@[simp]
lemma compare_mul_left_of_pos {α : Type*} [LinearOrder α] [Semiring α] [IsStrictOrderedRing α]
    {a b c : α} (h : 0 < c) : compare (c * a) (c * b) = compare a b :=
  compare_eq_compare_of_le (mul_le_mul_iff_of_pos_left h) (mul_le_mul_iff_of_pos_left h)

@[simp]
lemma compare_mul_right_of_pos {α : Type*} [LinearOrder α] [Semiring α] [IsStrictOrderedRing α]
    {a b c : α} (h : 0 < c) : compare (a * c) (b * c) = compare a b :=
  compare_eq_compare_of_le (mul_le_mul_iff_of_pos_right h) (mul_le_mul_iff_of_pos_right h)

@[simp, norm_cast]
lemma compare_natCast {α : Type*} [LinearOrder α] [Semiring α] [IsStrictOrderedRing α] {a b : ℕ} :
    compare (a : α) (b : α) = compare a b :=
  compare_eq_compare_of_le Nat.cast_le Nat.cast_le

@[simp, norm_cast]
lemma compare_intCast {α : Type*} [LinearOrder α] [Ring α] [IsStrictOrderedRing α] {a b : ℤ} :
    compare (a : α) (b : α) = compare a b :=
  compare_eq_compare_of_le Int.cast_le Int.cast_le

@[simp, norm_cast]
lemma compare_realToEReal {a b : ℝ} : compare (a : EReal) (b : EReal) = compare a b :=
  compare_eq_compare_of_le EReal.coe_le_coe_iff EReal.coe_le_coe_iff

@[simp, norm_cast]
lemma compare_nnrealToReal {a b : NNReal} : compare (a : ℝ) (b : ℝ) = compare a b :=
  compare_eq_compare_of_le NNReal.coe_le_coe NNReal.coe_le_coe

@[simp, norm_cast]
lemma compare_nnrealToENNReal {a b : NNReal} : compare (a : ENNReal) (b : ENNReal) = compare a b :=
  compare_eq_compare_of_le ENNReal.coe_le_coe ENNReal.coe_le_coe

@[simp]
lemma compare_erealNeg {a b : EReal} : compare (-a) (-b) = compare b a :=
  compare_eq_compare_of_le EReal.neg_le_neg_iff EReal.neg_le_neg_iff

lemma Nat.floor_div_natCast {α : Type*} [Semifield α] [LinearOrder α]
    [FloorSemiring α] [IsStrictOrderedRing α]
    (x : α) (n : ℕ) : ⌊x / n⌋₊ = ⌊x⌋₊ / n := by
  by_cases! hn : n = 0
  · simp_all
  simpa [hn] using (Nat.mul_cast_floor_div_cancel hn (x / n)).symm

lemma Nat.floor_div_two_pow {α : Type*} [Semifield α] [LinearOrder α]
    [FloorSemiring α] [IsStrictOrderedRing α]
    (x : α) (n : ℕ) : ⌊x / 2 ^ n⌋₊ = ⌊x⌋₊ >>> n := by
  norm_cast
  rw [Nat.floor_div_natCast, Nat.shiftRight_eq_div_pow]

@[simp]
lemma Nat.floor_intCast {α : Type*} [Ring α] [LinearOrder α] [FloorRing α]
    [IsOrderedRing α] (n : ℤ) : ⌊(n : α)⌋₊ = n.toNat := by
  simp [← Int.floor_toNat, Int.floor_intCast]

@[simp, norm_cast]
lemma Nat.floor_nnrealCoe (n : NNReal) : ⌊(n : ℝ)⌋₊ = ⌊n⌋₊ := (rfl)

@[simp, norm_cast]
lemma Int.floor_nnrealCoe (n : NNReal) : ⌊(n : ℝ)⌋ = ⌊n⌋₊ := by
  simp [← Int.floor_toNat, ← Nat.floor_nnrealCoe, Int.floor_nonneg]

lemma UInt8.toNat_ofNatClamp (n : Nat) :
    (UInt8.ofNatClamp n).toNat = min n 0xFF := by
  simp [ofNatClamp, apply_dite toNat]; lia

lemma UInt16.toNat_ofNatClamp (n : Nat) :
    (UInt16.ofNatClamp n).toNat = min n 0xFFFF := by
  simp [ofNatClamp, apply_dite toNat]; lia

lemma UInt32.toNat_ofNatClamp (n : Nat) :
    (UInt32.ofNatClamp n).toNat = min n 0xFFFF_FFFF := by
  simp [ofNatClamp, apply_dite toNat]; lia

lemma UInt64.toNat_ofNatClamp (n : Nat) :
    (UInt64.ofNatClamp n).toNat = min n 0xFFFF_FFFF_FFFF_FFFF := by
  simp [ofNatClamp, apply_dite toNat]; lia

lemma USize.toNat_ofNatClamp (n : Nat) :
    (USize.ofNatClamp n).toNat = min n (USize.size - 1) := by
  simp [ofNatClamp, apply_dite toNat]; lia

lemma Int8.toInt_ofIntClamp_eq_max (n : Int) :
    (Int8.ofIntClamp n).toInt = max (-0x80) (min 0x7f n) := by
  simp [ofIntClamp, apply_dite toInt]; lia

lemma Int16.toInt_ofIntClamp_eq_max (n : Int) :
    (Int16.ofIntClamp n).toInt = max (-0x8000) (min 0x7fff n) := by
  simp [ofIntClamp, apply_dite toInt]; lia

lemma Int32.toInt_ofIntClamp_eq_max (n : Int) :
    (Int32.ofIntClamp n).toInt = max (-0x8000_0000) (min 0x7fff_ffff n) := by
  simp [ofIntClamp, apply_dite toInt]; lia

lemma Int64.toInt_ofIntClamp_eq_max (n : Int) :
    (Int64.ofIntClamp n).toInt = max (-0x8000_0000_0000_0000) (min 0x7fff_ffff_ffff_ffff n) := by
  simp [ofIntClamp, apply_dite toInt]; lia

lemma ISize.toInt_ofIntClamp_eq_max (n : Int) :
    (ISize.ofIntClamp n).toInt = max ISize.minValue.toInt (min ISize.maxValue.toInt n) := by
  simp only [ofIntClamp, toInt_minValue, toInt_maxValue, apply_dite toInt, toInt_ofIntLE,
    dite_eq_ite]
  have : 0 < 2 ^ (System.Platform.numBits - 1) := Nat.two_pow_pos _
  grind

@[to_additive]
lemma zpow_le_zpow_left_of_nonpos {α : Type*} [CommGroup α]
    [PartialOrder α] [IsOrderedMonoid α] {n : ℤ} {a b : α} (hn : n ≤ 0)
    (h : a ≤ b) : b ^ n ≤ a ^ n := by
  rw [← neg_neg n, zpow_neg a, zpow_neg b]
  grw [h]
  rwa [neg_nonneg]

lemma zpow_le_zpow_left_of_nonpos₀ {α : Type*} [GroupWithZero α]
    [PartialOrder α] [PosMulReflectLT α] [MulPosReflectLT α] [MulPosMono α]
    [ZeroLEOneClass α]
    {n : ℤ} {a b : α} (hn : n ≤ 0) (ha : 0 < a) (h : a ≤ b) :
    b ^ n ≤ a ^ n := by
  rw [← neg_neg n, zpow_neg a, zpow_neg b]
  apply inv_anti₀ (zpow_pos ha (-n))
  exact zpow_le_zpow_left₀ (by simpa) ha.le h
