module
public import LeanFloats.UnpackedFloat.Valid
public import LeanFloats.UnpackedFloat.Rounding

namespace LeanFloats.UnpackedFloat

open Float.Model

variable {fmt : CommonFormat}

lemma ofUnpackedFloat_add {x y : UnpackedFloat}
    (hx : IsValid fmt.toFormat x) (hy : IsValid fmt.toFormat y) :
    ofUnpackedFloat (.add fmt.toFormat x y) =
      (ofUnpackedFloat x : RealFloat fmt.toFloatFormat).add (ofUnpackedFloat y) := by
  fun_cases UnpackedFloat.add
  · simp
  · simp
  · simp_all
  · simp_all [RealFloat.infinity_add_infinity]
  · cases y <;> simp_all [ofUnpackedFloat_finite_of_isValid]
  · cases x <;> simp_all [ofUnpackedFloat_finite_of_isValid]
  · rename_i s s' _; cases s' <;>
      simp_all [← RealFloat.zero_eq_ofValidNNReal, RealFloat.ofValidNNReal_neg_one_eq_neg_zero]
  · rename_i s s' _; cases s <;> cases s' <;>
      simp_all [← RealFloat.zero_eq_ofValidNNReal, RealFloat.ofValidNNReal_neg_one_eq_neg_zero]
  · rename_i s _ _ _
    cases s <;> cases y <;>
      simp_all [← RealFloat.zero_eq_ofValidNNReal, RealFloat.ofValidNNReal_neg_one_eq_neg_zero,
        RealFloat.zero_add_eq_ite, ofUnpackedFloat_finite_of_isValid, zpow_ne_zero, ne_of_gt]
  · rename_i s _ _ _
    cases s <;> cases x <;>
      simp_all [← RealFloat.zero_eq_ofValidNNReal, RealFloat.ofValidNNReal_neg_one_eq_neg_zero,
        RealFloat.add_zero_eq_ite, ofUnpackedFloat_finite_of_isValid, zpow_ne_zero, ne_of_gt]
  · rename_i s m e hm s' m₂ e₂ hm₂ emin m₃ e₃ h₁ m₄ e₄ h₂ m₅
    have hm₃ := decreaseExponent_eq_min h₁
    have he₃ := decreaseExponent_eq h₁
    have hm₄ := decreaseExponent_eq_min h₂
    have he₄ := decreaseExponent_eq h₂
    have hm₄_pos : 0 < m₄ := by by_contra! heq; simp_all [zpow_ne_zero, hm₂.ne']
    simp +contextual [ofUnpackedFloat_finite_of_isValid, m₅, add_mul, mul_assoc, emin, RealFloat.add,
      ← not_imp_not (a := _ ∨ _), SimpleSign.ne_iff_eq_neg, ← neg_add_rev, *]
    simp (disch := positivity) [ne_of_gt]

@[simp]
lemma ofUnpackedFloat_neg (x : UnpackedFloat) :
    ofUnpackedFloat x.neg = -(ofUnpackedFloat x : RealFloat fmt.toFloatFormat) := by
  fun_cases ofUnpackedFloat <;> simp [UnpackedFloat.neg, ofUnpackedFloat_finite]

lemma sub_eq_add_neg (x y : UnpackedFloat) (fmt : Format) : x.sub fmt y = x.add fmt y.neg := by
  cases x <;> cases y <;> simp [UnpackedFloat.add, UnpackedFloat.neg, UnpackedFloat.sub, Int.add_neg_eq_sub]

lemma ofUnpackedFloat_sub {x y : UnpackedFloat}
    (hx : IsValid fmt.toFormat x) (hy : IsValid fmt.toFormat y) :
    ofUnpackedFloat (.sub fmt.toFormat x y) =
      (ofUnpackedFloat x : RealFloat fmt.toFloatFormat).sub (ofUnpackedFloat y) := by
  simp [sub_eq_add_neg, ofUnpackedFloat_add, hx, hy.neg]

end UnpackedFloat

noncomputable def RealFloat.ofFloat (f : Float) : RealFloat .binary64 :=
  UnpackedFloat.ofUnpackedFloat (fmt := .binary64) f.toModel.unpack

noncomputable def RealFloat.ofFloat32 (f : Float32) : RealFloat .binary32 :=
  UnpackedFloat.ofUnpackedFloat (fmt := .binary32) f.toModel.unpack

noncomputable def RealFloat.toFloat (f : RealFloat .binary64) : Float :=
  .ofModel <| .pack (UnpackedFloat.toUnpackedFloat (fmt := .binary64) f)

noncomputable def RealFloat.toFloat32 (f : RealFloat .binary32) : Float32 :=
  .ofModel <| .pack (UnpackedFloat.toUnpackedFloat (fmt := .binary32) f)

@[simp]
lemma RealFloat.toFloat_ofFloat (f : Float) :
    (ofFloat f).toFloat = f := by
  rw [← Float.toBits_inj, ← UInt64.toBitVec_inj]
  simp [Float.toBits, toFloat, Float.Model.pack, ofFloat,
    Float.Model.unpack, UnpackedFloat.toUnpackedFloat_ofUnpackedFloat,
    Float.Model.UnpackedFloat.pack_unpack_of_valid f.toModel.valid]

@[simp]
lemma RealFloat.toFloat32_ofFloat32 (f : Float32) :
    (ofFloat32 f).toFloat32 = f := by
  rw [← Float32.toBits_inj, ← UInt32.toBitVec_inj]
  simp [Float32.toBits, toFloat32, Float32.Model.pack, ofFloat32,
    Float32.Model.unpack, UnpackedFloat.toUnpackedFloat_ofUnpackedFloat,
    Float.Model.UnpackedFloat.pack_unpack_of_valid f.toModel.valid]

@[simp]
lemma RealFloat.ofFloat_toFloat (f : RealFloat .binary64) :
    ofFloat f.toFloat = f := by
  simp [ofFloat, toFloat, Float.Model.pack, Float.Model.unpack, UnpackedFloat.unpack_pack,
    UnpackedFloat.isValid_toUnpackedFloat (fmt := .binary64)]

@[simp]
lemma RealFloat.ofFloat32_toFloat32 (f : RealFloat .binary32) :
    ofFloat32 f.toFloat32 = f := by
  simp [ofFloat32, toFloat32, Float32.Model.pack, Float32.Model.unpack, UnpackedFloat.unpack_pack,
    UnpackedFloat.isValid_toUnpackedFloat (fmt := .binary32)]

end LeanFloats
