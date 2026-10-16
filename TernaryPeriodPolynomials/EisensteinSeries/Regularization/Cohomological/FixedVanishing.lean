module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.WeightOperators
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Gamma.OneThreeAdelicVanishing

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cuspLowering_mem_finiteFixed (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (vector : cuspFiniteFixedSubmodule cusp level) :
    cuspLoweringOperator cusp vector.val ∈ cuspFiniteFixedSubmodule cusp level := by
  exact Submodule.sub_mem _
    (cuspDerivedAction_finiteFixed cusp level binarySplitDirection vector)
    (Submodule.smul_mem _ Complex.I
      (cuspDerivedAction_finiteFixed cusp level binarySymmetricDirection vector))

theorem cohomological_finiteFixed_naturalWeight_zero
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (level : Subgroup BinaryFiniteGL)
    (bottom_zero : ∀ vector : cuspFiniteFixedSubmodule cusp level,
      cuspRotationOperator cusp vector.val = (Complex.I * ((degree : ℂ) + 3)) • vector.val → vector.val = 0)
    (weight : ℕ) (vector : cuspFiniteFixedSubmodule cusp level)
    (rotation : cuspRotationOperator cusp vector.val = (Complex.I * (weight : ℂ)) • vector.val) : vector.val = 0 := by
  induction weight using Nat.strong_induction_on generalizing vector with
  | h weight induction =>
    rcases lt_trichotomy weight (degree + 3) with below | bottom | above
    · by_contra nonzero
      obtain ⟨step, spectrum⟩ := cohomological_integer_weight_spectrum cohomological weight vector.val nonzero
        (by simpa only [Int.cast_natCast] using rotation)
      simp only [Int.natAbs_natCast] at spectrum
      omega
    · apply bottom_zero vector
      simpa only [bottom, Nat.cast_add, Nat.cast_ofNat] using rotation
    · have smaller : weight - 2 < weight := by omega
      have lowered := induction (weight - 2) smaller
        ⟨cuspLoweringOperator cusp vector.val, cuspLowering_mem_finiteFixed cusp level vector⟩
      have cast : ((weight - 2 : ℕ) : ℂ) = (weight : ℂ) - 2 := by
        rw [Nat.cast_sub (by omega), Nat.cast_ofNat]
      have lowered_rotation : cuspRotationOperator cusp (cuspLoweringOperator cusp vector.val) =
          (Complex.I * ((weight - 2 : ℕ) : ℂ)) • cuspLoweringOperator cusp vector.val := by
        rw [cast]
        exact cuspLowering_weight cusp weight vector.val rotation
      have zero := lowered lowered_rotation
      by_contra nonzero
      exact cohomological_lowering_nonzero_above cohomological weight (by exact_mod_cast above)
        vector.val nonzero (by simpa only [Complex.ofReal_natCast] using rotation) zero

theorem cohomological_finiteFixed_weight_zero
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (level : Subgroup BinaryFiniteGL)
    (bottom_zero : ∀ vector : cuspFiniteFixedSubmodule cusp level,
      cuspRotationOperator cusp vector.val = (Complex.I * ((degree : ℂ) + 3)) • vector.val → vector.val = 0)
    (weight : ℤ) (vector : cuspFiniteFixedSubmodule cusp level)
    (rotation : cuspRotationOperator cusp vector.val = (Complex.I * (weight : ℂ)) • vector.val) : vector.val = 0 := by
  by_cases nonnegative : 0 ≤ weight
  · lift weight to ℕ using nonnegative
    exact cohomological_finiteFixed_naturalWeight_zero cohomological level bottom_zero weight vector
      (by simpa only [Int.cast_natCast] using rotation)
  · let reflected : cuspFiniteFixedSubmodule cusp level :=
      ⟨cuspSmoothAction cusp (atInfinity binaryReflection) vector.val,
        cuspHilbertFiniteFixedSubmodule_real_stable cusp level binaryReflection vector.property⟩
    have reflected_rotation : cuspRotationOperator cusp reflected.val =
        (Complex.I * ((-weight).toNat : ℂ)) • reflected.val := by
      have cast : ((-weight).toNat : ℂ) = ((-weight : ℤ) : ℂ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
      rw [cast]
      change cuspRotationOperator cusp (cuspSmoothAction cusp (atInfinity binaryReflection) vector.val) = _
      rw [cuspRotation_reflection, rotation, map_smul, ← neg_smul, Int.cast_neg, mul_neg]
    have zero := cohomological_finiteFixed_naturalWeight_zero cohomological level bottom_zero
      (-weight).toNat reflected reflected_rotation
    by_contra nonzero
    exact cuspSmoothAction_ne_zero cusp _ vector.val nonzero zero

theorem cohomological_finiteFixed_zero_of_bottom_zero
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (level : Subgroup BinaryFiniteGL)
    (bottom_zero : ∀ vector : cuspFiniteFixedSubmodule cusp level,
      cuspRotationOperator cusp vector.val = (Complex.I * ((degree : ℂ) + 3)) • vector.val → vector.val = 0)
    (vector : cuspFiniteFixedSubmodule cusp level) : vector.val = 0 := by
  apply Subtype.ext
  apply cuspRotationProjection_complete cusp vector.val.val
  intro weight
  have projected_fixed : cuspSmoothRotationProjection cusp weight vector.val ∈ cuspFiniteFixedSubmodule cusp level := by
    intro matrix
    exact cuspRotationProjection_finite_fixed cusp weight vector.val.val matrix.val (vector.property matrix)
  have zero := cohomological_finiteFixed_weight_zero cohomological level bottom_zero weight
    ⟨cuspSmoothRotationProjection cusp weight vector.val, projected_fixed⟩
    (cuspSmoothRotationProjection_eigenvector cusp weight vector.val)
  exact congrArg Subtype.val zero

theorem cohomological_small_degree_fixed_zero
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (small : degree < 3) (level : Subgroup BinaryFiniteGL)
    (principal_included : binaryPrincipalLevel ≤ level)
    (gamma_included : ∀ matrix ∈ CongruenceSubgroup.Gamma1 3,
      SpecialLinearGroup.mapGL FiniteAdeles matrix ∈ level)
    (reflection_included : GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) binaryIntegralRowReflection ∈ level)
    (vector : cuspFiniteFixedSubmodule cusp level) : vector.val = 0 := by
  apply cohomological_finiteFixed_zero_of_bottom_zero cohomological level _ vector
  intro lowest rotation
  let principal : cuspPrincipalLowestSubmodule cusp (degree + 3) :=
    ⟨lowest.val, (fun matrix => lowest.property ⟨matrix.val, principal_included matrix.property⟩),
      by simpa only [Nat.cast_add, Nat.cast_ofNat] using rotation,
      cohomological_bottom_lowering_zero cohomological lowest.val rotation⟩
  have zero := cuspPrincipalLowest_zero_of_gammaOneThree_fixed cohomological (degree + 3) (by omega) (by omega)
    principal (fun matrix member => Subtype.ext (lowest.property ⟨_, gamma_included matrix member⟩))
    (Subtype.ext (lowest.property ⟨_, reflection_included⟩))
  exact congrArg Subtype.val zero

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
