module
public import Mathlib.Data.EReal.Operations
public import Mathlib.Data.Sign.Defs
public import Mathlib.Data.Int.Log
public import Mathlib.Data.Nat.Bitwise

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
