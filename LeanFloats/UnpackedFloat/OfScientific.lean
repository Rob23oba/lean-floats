module
public import LeanFloats.UnpackedFloat.Operations
import all Init.Data.OfScientific

public section

namespace LeanFloats

namespace UnpackedFloat

open Float.Model

@[simp]
lemma ofUnbounded_toUnboundedFloat_ofScientific {fmt fmt' common} [HasCommonOfFormat fmt common]
    [HasCommonOfFloatFormat fmt' common] (m : ℕ) (e : ℤ) :
    RealFloat.ofUnbounded (toUnboundedFloat (UnpackedFloat.ofScientific fmt m e)) =
      (RealFloat.roundReal (m * 10 ^ e) : RealFloat fmt') := by
  cases HasCommonOfFormat.elim fmt
  cases HasCommonOfFloatFormat.elim fmt'
  fun_cases UnpackedFloat.ofScientific
  · simp_all [RealFloat.roundReal_eq_ofValidReal, RealFloat.ofValidReal_def,
      RealFloat.ofUnbounded_eq_ofUnboundedInRange]
  · rename_i he
    rw [toUnboundedFloat_infinity, ofSign_positive, RealFloat.ofUnbounded_infinity,
      eq_comm, ← RealFloat.infinity_one_le_iff]
    have : 2 ^ common.toFormat.infinityExponent ≤ (m * 10 ^ e : ℝ) := by
      grw [he, Format.infinityExponent, ← Nat.one_le_iff_ne_zero.mpr ‹m ≠ 0›,
        show (2 : ℝ) ≤ (10 : ℝ) by norm_num, Nat.sub_le, Nat.cast_one, one_mul,
        ← zpow_natCast, Nat.cast_pow, Nat.cast_ofNat] <;> norm_num
    rw [RealFloat.roundReal_of_ge_base_pow_infExp (by simpa using this)]
    simp [RealFloat.overflowValue]
  · rename_i he
    suffices RoundingFunction.tiesToEven (m * 10 ^ e / 2 ^ common.toFloatFormat.getExponent (m * 10 ^ e)) = 0 by
      simp [← RealFloat.ofUnbounded_roundReal, UnboundedFloat.roundReal, this,
        SimpleSign.ofValue_of_nonneg, mul_nonneg_iff]
    rw [← zero_add (_ / _), ← Int.cast_zero, RoundingFunction.tiesToEven.apply_intCast_add_of_abs_lt]
    have : (m * 10 ^ e : ℝ) < 2 ^ (common.toFloatFormat.minExp - 1) := by
      grw [he, zpow_le_zpow_left_of_nonpos₀ (a := 2) (b := 10) (neg_nonpos.mpr (by positivity)) two_pos (by norm_num),
        @Nat.lt_log2_self m]
      · simp [← zpow_natCast, ← zpow_add₀]
        have : 2 ^ common.ebits = 2 * 2 ^ (common.ebits - 1) := by simp [← pow_succ']; format_trivial
        simp only [FloatFormat.minExp] at *
        grind [common.mbits_lt]
      · norm_num
    rw [FloatFormat.getExponent_eq_minExp_iff.mpr]
    · simpa [abs_div, div_lt_iff₀', ← zpow_sub_one₀] using this
    · simp only [abs_mul, Nat.abs_cast, abs_zpow, Nat.abs_ofNat, Base.value_ofNat, Nat.cast_ofNat,
        Nat.cast_add, Nat.cast_one]
      grw [this, zpow_le_zpow_iff_right₀ (by norm_num)]
      simp +arith
  · rw [UnpackedFloat.mul, toUnboundedFloat_roundWithAccuracy (f := 0) _ (.exact rfl)]
    · simp [RealFloat.roundNNReal_eq_roundReal, Nat.shiftLeft_eq, *, ← zpow_natCast,
        mul_assoc, mul_left_comm (2 ^ (_ : ℤ)) (10 ^ e : ℝ), ← zpow_add₀]
    · simp [totalExponent, *, Format.targetExponent, CommonFormat.toFloatFormat] at *
      have := @Nat.log2_add_log2_le_log2_mul (m <<< (common.mbits + 1)) (10 ^ e.toNat) (by simpa) (by simp)
      simp [*] at this
      format_trivial
  · rw [toUnboundedFloat_div_finite]
    simp [RealFloat.roundNNReal_eq_roundReal, ← zpow_natCast, le_of_not_ge, *]

@[simp]
lemma isRounded_ofScientific {fmt common} [HasCommonOfFormat fmt common] (m : ℕ) (e : ℤ) :
    IsRounded fmt (UnpackedFloat.ofScientific fmt m e) := by
  fun_cases UnpackedFloat.ofScientific <;> try simp [isRounded_div]
  rw [UnpackedFloat.mul]
  apply isRounded_roundWithAccuracy
  simp [totalExponent, *, Format.targetExponent] at *
  cases HasCommonOfFormat.elim fmt
  have := @Nat.log2_add_log2_le_log2_mul (m <<< (common.mbits + 1)) (10 ^ e.toNat) (by simpa) (by simp)
  simp [*] at this
  format_trivial

end UnpackedFloat

namespace RealFloat

private lemma isValidFloat_binary64_ten_pow {i : Nat} (h : i < 23) :
    FloatFormat.binary64.IsValidFloat (10 ^ i) := by
  suffices FloatFormat.binary64.IsValidFloat ((5 ^ i : ℤ) * 2 ^ (i : ℤ)) by
    norm_num [← mul_pow] at this
    simpa
  refine .intro_lt (by grind) (by grind) ?_
  grw [Int.natAbs_pow, Nat.le_sub_one_of_lt h] <;> decide

private lemma isValidFloat_binary32_ten_pow {i : Nat} (h : i < 11) :
    FloatFormat.binary32.IsValidFloat (10 ^ i) := by
  suffices FloatFormat.binary32.IsValidFloat ((5 ^ i : ℤ) * 2 ^ (i : ℤ)) by
    norm_num [← mul_pow] at this
    simpa
  refine .intro_lt (by grind) (by grind) ?_
  grw [Int.natAbs_pow, Nat.le_sub_one_of_lt h] <;> decide

private lemma ofFloat_getElem_exactlyRepresentablePowersOfTen
    {i : Nat} (h : i < Float.exactlyRepresentablePowersOfTen.size) :
    ofFloat Float.exactlyRepresentablePowersOfTen[i] =
      .ofValidNNReal 1 (10 ^ i) (by simpa using isValidFloat_binary64_ten_pow h) := by
  have : Float.exactlyRepresentablePowersOfTen[i] = .ofModel (.ofNat (10 ^ i)) := by
    decide +revert
  simp [this, ofFloat, Float.Model.ofNat, Float.Model.pack, Float.Model.unpack,
    roundReal_eq_ofValidReal, isValidFloat_binary64_ten_pow h, ofValidNNReal_eq_ofValidReal]

private lemma ofFloat32_getElem_exactlyRepresentablePowersOfTen
    {i : Nat} (h : i < Float32.exactlyRepresentablePowersOfTen.size) :
    ofFloat32 Float32.exactlyRepresentablePowersOfTen[i] =
      .ofValidNNReal 1 (10 ^ i) (by simpa using isValidFloat_binary32_ten_pow h) := by
  have : Float32.exactlyRepresentablePowersOfTen[i] = .ofModel (.ofNat (10 ^ i)) := by
    decide +revert
  simp [this, ofFloat32, Float32.Model.ofNat, Float32.Model.pack, Float32.Model.unpack,
    roundReal_eq_ofValidReal, isValidFloat_binary32_ten_pow h, ofValidNNReal_eq_ofValidReal]

@[simp]
lemma ofFloat_ofScientific (m : Nat) (s : Bool) (e : Nat) :
    ofFloat (OfScientific.ofScientific m s e) = .roundReal (OfScientific.ofScientific m s e) := by
  rw [NNRatCast.ofScientific_eq_ite]
  simp only [OfScientific.ofScientific]
  fun_cases Float.ofScientific
  · rename_i hrange pow hs
    subst pow
    rw [ofFloat_div, ofFloat_ofUInt64, UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hrange.1 (by decide)),
      if_pos hs, NNRat.cast_divNat, ofFloat_getElem_exactlyRepresentablePowersOfTen,
      roundReal_eq_ofValidReal (FloatFormat.isValidFloat_natCast (mod_cast hrange.1.le)),
      ofValidReal_def]
    simp [SimpleSign.ofValue_of_nonneg, ofValidNNReal_div_ofValidNNReal, roundNNReal_eq_roundReal]
  · rename_i hrange pow hs
    subst pow
    rw [ofFloat_mul, ofFloat_ofUInt64, UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hrange.1 (by decide)),
      if_neg hs, ofFloat_getElem_exactlyRepresentablePowersOfTen,
      roundReal_eq_ofValidReal (FloatFormat.isValidFloat_natCast (mod_cast hrange.1.le)),
      ofValidReal_def]
    simp [SimpleSign.ofValue_of_nonneg, ofValidNNReal_mul_ofValidNNReal, roundNNReal_eq_roundReal]
  · cases s <;>
      simp +zetaDelta [ofFloat, Float.Model.unpack, Float.Model.ofScientific, Float.Model.pack,
        Int.negOfNat_eq, div_eq_mul_inv]

@[simp]
lemma ofFloat32_ofScientific (m : Nat) (s : Bool) (e : Nat) :
    ofFloat32 (OfScientific.ofScientific m s e) = .roundReal (OfScientific.ofScientific m s e) := by
  rw [NNRatCast.ofScientific_eq_ite]
  simp only [OfScientific.ofScientific]
  fun_cases Float32.ofScientific
  · rename_i hrange pow hs
    subst pow
    rw [ofFloat32_div, ofFloat32_ofUInt64, UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hrange.1 (by decide)),
      if_pos hs, NNRat.cast_divNat, ofFloat32_getElem_exactlyRepresentablePowersOfTen,
      roundReal_eq_ofValidReal (FloatFormat.isValidFloat_natCast (mod_cast hrange.1.le.trans (by simp))),
      ofValidReal_def]
    simp [SimpleSign.ofValue_of_nonneg, ofValidNNReal_div_ofValidNNReal, roundNNReal_eq_roundReal]
  · rename_i hrange pow hs
    subst pow
    rw [ofFloat32_mul, ofFloat32_ofUInt64, UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hrange.1 (by decide)),
      if_neg hs, ofFloat32_getElem_exactlyRepresentablePowersOfTen,
      roundReal_eq_ofValidReal (FloatFormat.isValidFloat_natCast (mod_cast hrange.1.le.trans (by simp))),
      ofValidReal_def]
    simp [SimpleSign.ofValue_of_nonneg, ofValidNNReal_mul_ofValidNNReal, roundNNReal_eq_roundReal]
  · cases s <;>
      simp +zetaDelta [ofFloat32, Float32.Model.unpack, Float32.Model.ofScientific, Float32.Model.pack,
        Int.negOfNat_eq, div_eq_mul_inv]

@[simp]
lemma ofFloat_ofNat (n : Nat) : ofFloat (.ofNat n) = roundReal n := by
  simp [Float.ofNat, NNRatCast.ofScientific_eq_ite]

@[simp]
lemma ofFloat32_ofNat (n : Nat) : ofFloat32 (.ofNat n) = roundReal n := by
  simp [Float32.ofNat, NNRatCast.ofScientific_eq_ite]

@[simp]
lemma ofFloat_ofNat' (n : Nat) : ofFloat ofNat(n) = ofNat(n) := by
  change ofFloat (.ofNat n) = roundReal n
  simp

@[simp]
lemma ofFloat32_ofNat' (n : Nat) : ofFloat32 ofNat(n) = ofNat(n) := by
  change ofFloat32 (.ofNat n) = roundReal n
  simp

@[simp]
lemma ofFloat_ofInt (n : Int) : ofFloat (.ofInt n) = roundReal n := by
  cases n <;> simp [Float.ofInt, show Float.neg = (-·) by rfl]; norm_cast; lia

@[simp]
lemma ofFloat32_ofInt (n : Int) : ofFloat32 (.ofInt n) = roundReal n := by
  cases n <;> simp [Float32.ofInt, show Float32.neg = (-·) by rfl]; norm_cast; lia

end LeanFloats.RealFloat
