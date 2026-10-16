module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.LowestDimension

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

def cuspPrincipalWeightSubmodule (cusp : CuspidalRepresentation) (weight : ℤ) : Submodule ℂ cusp.smooth where
  carrier := {vector | vector ∈ cuspFiniteFixedSubmodule cusp binaryPrincipalLevel ∧
    cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector}
  zero_mem' := ⟨Submodule.zero_mem _, by simp⟩
  add_mem' {first second} first_member second_member :=
    ⟨Submodule.add_mem _ first_member.1 second_member.1, by
      rw [map_add, first_member.2, second_member.2, smul_add]⟩
  smul_mem' scalar vector member := ⟨Submodule.smul_mem _ scalar member.1, by
    rw [map_smul, member.2, smul_comm]⟩

theorem cuspLowering_finiteFixed (cusp : CuspidalRepresentation)
    (vector : cuspFiniteFixedSubmodule cusp binaryPrincipalLevel) :
    cuspLoweringOperator cusp vector.val ∈ cuspFiniteFixedSubmodule cusp binaryPrincipalLevel := by
  exact Submodule.sub_mem _
    (cuspDerivedAction_finiteFixed cusp binaryPrincipalLevel binarySplitDirection vector)
    (Submodule.smul_mem _ Complex.I
      (cuspDerivedAction_finiteFixed cusp binaryPrincipalLevel binarySymmetricDirection vector))

noncomputable def cuspPrincipalWeightLowering (cusp : CuspidalRepresentation) (weight : ℤ) :
    cuspPrincipalWeightSubmodule cusp weight →ₗ[ℂ] cuspPrincipalWeightSubmodule cusp (weight - 2) where
  toFun vector := ⟨cuspLoweringOperator cusp vector.val,
    cuspLowering_finiteFixed cusp ⟨vector.val, vector.property.1⟩, by
      simpa only [Int.cast_sub, Int.cast_ofNat] using
        cuspLowering_weight cusp weight vector.val vector.property.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

noncomputable def cuspPrincipalWeightReflection (cusp : CuspidalRepresentation) (weight : ℤ) :
    cuspPrincipalWeightSubmodule cusp weight →ₗ[ℂ] cuspPrincipalWeightSubmodule cusp (-weight) where
  toFun vector := ⟨cuspSmoothAction cusp (atInfinity binaryReflection) vector.val, by
      exact cuspHilbertFiniteFixedSubmodule_real_stable cusp binaryPrincipalLevel binaryReflection vector.property.1,
    by
      rw [cuspRotation_reflection, vector.property.2, map_smul, ← neg_smul, Int.cast_neg, mul_neg]⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem cuspPrincipalWeightReflection_injective (cusp : CuspidalRepresentation) (weight : ℤ) :
    Function.Injective (cuspPrincipalWeightReflection cusp weight) := by
  intro first second equality
  apply Subtype.ext
  apply Subtype.ext
  exact (cuspUnitaryAction cusp (atInfinity binaryReflection)).injective
    (congrArg (fun vector : cuspPrincipalWeightSubmodule cusp (-weight) => vector.val.val) equality)

theorem cohomological_principal_lowering_injective
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (weight : ℤ) (above : (degree : ℤ) + 3 < weight) :
    Function.Injective (cuspPrincipalWeightLowering cusp weight) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro vector zero
  apply Subtype.ext
  by_contra nonzero
  have rotation : cuspRotationOperator cusp vector.val = (Complex.I * ((weight : ℝ) : ℂ)) • vector.val := by
    simpa only [Complex.ofReal_intCast] using vector.property.2
  exact cohomological_lowering_nonzero_above cohomological weight (by exact_mod_cast above)
    vector.val nonzero rotation (congrArg Subtype.val zero)

theorem cohomological_bottom_lowering_zero
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * ((degree : ℂ) + 3)) • vector) :
    cuspLoweringOperator cusp vector = 0 := by
  have rotation_real : cuspRotationOperator cusp vector =
      (Complex.I * (((degree : ℝ) + 3 : ℝ) : ℂ)) • vector := by
    simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_ofNat] using rotation
  have norm_formula := cuspLowering_norm_sq_of_eigenvectors cusp ((degree : ℝ) + 3)
    (((degree : ℝ) + 1) * ((degree : ℝ) + 3)) vector rotation_real
    (cohomological_casimir_eigenvector cohomological vector)
  have coefficient : ((degree : ℝ) + 3) ^ 2 - 2 * ((degree : ℝ) + 3) -
      ((degree : ℝ) + 1) * ((degree : ℝ) + 3) = 0 := by ring
  rw [coefficient, zero_mul] at norm_formula
  apply Subtype.ext
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (cuspLoweringOperator cusp vector).val]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
