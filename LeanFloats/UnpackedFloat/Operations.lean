module
public import LeanFloats.UnpackedFloat.Valid
public import LeanFloats.UnpackedFloat.Rounding

namespace LeanFloats.UnpackedFloat

open Float.Model

variable {fmt : CommonFormat}

lemma toUnboundedFloat_add {fmt fmt' common}
    [HasCommonOfFormat fmt common] [HasCommonOfFloatFormat fmt' common]
    {x y : UnpackedFloat}
    (hx : IsRounded fmt x) (hy : IsRounded fmt y) :
    toUnboundedFloat (.add fmt x y) =
      (toUnboundedFloat x : UnboundedFloat fmt').add (toUnboundedFloat y) := by
  cases HasCommonOfFormat.elim fmt
  cases HasCommonOfFloatFormat.elim fmt'
  fun_cases UnpackedFloat.add
  · simp
  · simp
  · simp_all
  · simp_all [UnboundedFloat.infinity_add_infinity]
  · cases y <;> simp_all [toUnboundedFloat_finite_of_isRounded]
  · cases x <;> simp_all [toUnboundedFloat_finite_of_isRounded]
  · rename_i s s' _; cases s' <;>
      simp_all [← UnboundedFloat.zero_eq_ofValidNNReal, UnboundedFloat.ofValidNNReal_neg_one_eq_neg_zero]
  · rename_i s s' _; cases s <;> cases s' <;>
      simp_all [← UnboundedFloat.zero_eq_ofValidNNReal, UnboundedFloat.ofValidNNReal_neg_one_eq_neg_zero]
  · rename_i s _ _ _
    cases s <;> cases y <;>
      simp_all [← UnboundedFloat.zero_eq_ofValidNNReal, UnboundedFloat.ofValidNNReal_neg_one_eq_neg_zero,
        UnboundedFloat.zero_add_eq_ite, toUnboundedFloat_finite_of_isRounded, zpow_ne_zero, ne_of_gt]
  · rename_i s _ _ _
    cases s <;> cases x <;>
      simp_all [← UnboundedFloat.zero_eq_ofValidNNReal, UnboundedFloat.ofValidNNReal_neg_one_eq_neg_zero,
        UnboundedFloat.add_zero_eq_ite, toUnboundedFloat_finite_of_isRounded, zpow_ne_zero, ne_of_gt]
  · rename_i s m e hm s' m₂ e₂ hm₂ emin m₃ e₃ h₁ m₄ e₄ h₂ m₅
    have hm₃ := decreaseExponent_eq_min h₁
    have he₃ := decreaseExponent_eq h₁
    have hm₄ := decreaseExponent_eq_min h₂
    have he₄ := decreaseExponent_eq h₂
    have hm₄_pos : 0 < m₄ := by by_contra! heq; simp_all [zpow_ne_zero, hm₂.ne']
    simp +contextual [toUnboundedFloat_finite_of_isRounded, m₅, add_mul, mul_assoc, emin, UnboundedFloat.add,
      ← not_imp_not (a := _ ∨ _), SimpleSign.ne_iff_eq_neg, ← neg_add_rev, *]
    simp (disch := positivity) [ne_of_gt]

lemma isRounded_add {fmt : Format} {x y : UnpackedFloat}
    (hx : IsRounded fmt x) (hy : IsRounded fmt y) : IsRounded fmt (.add fmt x y) := by
  cases x <;> cases y <;> simp [UnpackedFloat.add] <;> (try split) <;> simp_all

@[simp]
lemma toUnboundedFloat_neg {fmt : FloatFormat 2} (x : UnpackedFloat) :
    toUnboundedFloat x.neg = -(toUnboundedFloat x : UnboundedFloat fmt) := by
  fun_cases toUnboundedFloat <;> simp [UnpackedFloat.neg, toUnboundedFloat_finite]

@[simp]
lemma sub_eq_add_neg (x y : UnpackedFloat) (fmt : Format) : x.sub fmt y = x.add fmt y.neg := by
  cases x <;> cases y <;> simp [UnpackedFloat.add, UnpackedFloat.neg, UnpackedFloat.sub, Int.add_neg_eq_sub]

lemma toUnboundedFloat_sub {x y : UnpackedFloat}
    (hx : IsRounded fmt.toFormat x) (hy : IsRounded fmt.toFormat y) :
    toUnboundedFloat (.sub fmt.toFormat x y) =
      (toUnboundedFloat x : UnboundedFloat fmt.toFloatFormat).sub (toUnboundedFloat y) := by
  simp [sub_eq_add_neg, toUnboundedFloat_add, hx, hy.neg]

end UnpackedFloat

lemma UnpackedFloat.CommonFormat.toFloatFormat_binary64 :
    toFloatFormat .binary64 = .binary64 := rfl

lemma UnpackedFloat.CommonFormat.toFloatFormat_binary32 :
    toFloatFormat .binary32 = .binary32 := rfl

lemma UnpackedFloat.CommonFormat.toFormat_binary64 :
    toFloatFormat .binary64 = .binary64 := rfl

lemma UnpackedFloat.CommonFormat.toFormat_binary32 :
    toFloatFormat .binary32 = .binary32 := rfl

noncomputable def RealFloat.ofFloat (f : Float) : RealFloat .binary64 :=
  ofUnbounded (UnpackedFloat.toUnboundedFloat (fmt := .binary64) f.toModel.unpack)

noncomputable def RealFloat.ofFloat32 (f : Float32) : RealFloat .binary32 :=
  ofUnbounded (UnpackedFloat.toUnboundedFloat (fmt := .binary32) f.toModel.unpack)

noncomputable def RealFloat.toFloat (f : RealFloat .binary64) : Float :=
  .ofModel <| .pack (UnpackedFloat.ofUnboundedFloat (fmt := .binary64) f.toUnbounded)

noncomputable def RealFloat.toFloat32 (f : RealFloat .binary32) : Float32 :=
  .ofModel <| .pack (UnpackedFloat.ofUnboundedFloat (fmt := .binary32) f.toUnbounded)

@[simp] lemma UnpackedFloat.two_le_exponentBits_binary32 : 2 ≤ UnpackedFloat.CommonFormat.binary32.toFormat.exponentBits := by decide
@[simp] lemma UnpackedFloat.two_le_exponentBits_binary64 : 2 ≤ UnpackedFloat.CommonFormat.binary64.toFormat.exponentBits := by decide

@[simp]
lemma RealFloat.toFloat_ofFloat (f : Float) :
    (ofFloat f).toFloat = f := by
  rw [← Float.toBits_inj, ← UInt64.toBitVec_inj]
  simp [Float.toBits, toFloat, Float.Model.pack, ofFloat,
    Float.Model.unpack, Float.Model.UnpackedFloat.pack_unpack_of_valid f.toModel.valid]

@[simp]
lemma RealFloat.toFloat32_ofFloat32 (f : Float32) :
    (ofFloat32 f).toFloat32 = f := by
  rw [← Float32.toBits_inj, ← UInt32.toBitVec_inj]
  simp [Float32.toBits, toFloat32, Float32.Model.pack, ofFloat32,
    Float32.Model.unpack, Float.Model.UnpackedFloat.pack_unpack_of_valid f.toModel.valid]

@[simp]
lemma RealFloat.ofFloat_toFloat (f : RealFloat .binary64) :
    ofFloat f.toFloat = f := by
  simp [ofFloat, toFloat, Float.Model.pack, Float.Model.unpack, UnpackedFloat.unpack_pack]

@[simp]
lemma RealFloat.ofFloat32_toFloat32 (f : RealFloat .binary32) :
    ofFloat32 f.toFloat32 = f := by
  simp [ofFloat32, toFloat32, Float32.Model.pack, Float32.Model.unpack]

@[simp]
lemma RealFloat.ofFloat_add (a b : Float) :
    ofFloat (a + b) = (ofFloat a).add (ofFloat b) := by
  simp [Float.add, ofFloat, Float.Model.unpack, · + ·, Add.add,
    Float.Model.add, Float.Model.pack, UnpackedFloat.isRounded_add,
    UnpackedFloat.toUnboundedFloat_add, RealFloat.add]

@[simp]
lemma RealFloat.ofFloat32_add (a b : Float32) :
    ofFloat32 (a + b) = (ofFloat32 a).add (ofFloat32 b) := by
  simp [Float32.add, ofFloat32, Float32.Model.unpack, · + ·, Add.add,
    Float32.Model.add, Float32.Model.pack, UnpackedFloat.isRounded_add,
    UnpackedFloat.toUnboundedFloat_add, RealFloat.add]

@[simp]
lemma RealFloat.ofFloat_neg (a : Float) :
    ofFloat (-a) = -(ofFloat a) := by
  change ofFloat (Float.ofModel a.toModel.neg) = _
  simp [ofFloat, Float.Model.unpack, Float.Model.neg, Float.Model.pack, neg_ofUnbounded]

@[simp]
lemma RealFloat.ofFloat32_neg (a : Float32) :
    ofFloat32 (-a) = -(ofFloat32 a) := by
  change ofFloat32 (Float32.ofModel a.toModel.neg) = _
  simp [ofFloat32, Float32.Model.unpack, Float32.Model.neg, Float32.Model.pack, neg_ofUnbounded]

@[simp]
lemma RealFloat.ofFloat_sub (a b : Float) :
    ofFloat (a - b) = (ofFloat a).sub (ofFloat b) := by
  simp (config := { maxDischargeDepth := 3 }) [Float.sub, ofFloat,
    Float.Model.unpack, · - ·, Sub.sub, Float.Model.sub, Float.Model.pack,
    UnpackedFloat.isRounded_add, UnpackedFloat.toUnboundedFloat_add, RealFloat.add]

@[simp]
lemma RealFloat.ofFloat32_sub (a b : Float32) :
    ofFloat32 (a - b) = (ofFloat32 a).sub (ofFloat32 b) := by
  simp (config := { maxDischargeDepth := 3 }) [Float32.sub, ofFloat32,
    Float32.Model.unpack, · - ·, Sub.sub, Float32.Model.sub, Float32.Model.pack,
    UnpackedFloat.isRounded_add, UnpackedFloat.toUnboundedFloat_add, RealFloat.add]

end LeanFloats
