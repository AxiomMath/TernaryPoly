module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.IntegralModularLevel

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

instance binaryRealPrincipalLevel_hasDetOne : binaryRealPrincipalLevel.HasDetOne where
  det_eq := by
    rintro matrix ⟨integralMatrix, _, rfl⟩
    exact SpecialLinearGroup.det_mapGL integralMatrix

theorem cohomological_principal_upperHalfForm_slash {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℕ)
    (vector : cuspFiniteFixedSubmodule cusp binaryPrincipalLevel)
    (rotation : cuspRotationOperator cusp vector.val = (Complex.I * (weight : ℂ)) • vector.val)
    (matrix : BinaryRealGL) (member : matrix ∈ binaryRealPrincipalLevel) :
    SlashAction.map (weight : ℤ) matrix (cuspUpperHalfForm cusp weight vector.val 1) =
      cuspUpperHalfForm cusp weight vector.val 1 := by
  obtain ⟨integralMatrix, integral_member, rfl⟩ := member
  rw [cohomological_upperHalfForm_slash cohomological weight vector.val rotation 1 _
    (by rw [SpecialLinearGroup.det_mapGL]; rfl), one_mul]
  exact cuspUpperHalfForm_integral_invariant cusp weight vector integralMatrix integral_member

theorem cohomological_upperHalfForm_zero_at_cusp {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℕ) (weight_positive : 0 < weight)
    (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (argument : BinaryAdelicGL) (cuspPoint : OnePoint ℝ)
    (is_cusp : IsCusp cuspPoint binaryRealPrincipalLevel) :
    cuspPoint.IsZeroAt (cuspUpperHalfForm cusp weight vector argument) (weight : ℤ) := by
  apply (OnePoint.isZeroAt_iff_forall_SL2Z
    (is_cusp.mono binaryRealPrincipalLevel_le_full)).mpr
  intro matrix _
  change UpperHalfPlane.IsZeroAtImInfty (SlashAction.map (weight : ℤ)
    (SpecialLinearGroup.mapGL ℝ matrix) (cuspUpperHalfForm cusp weight vector argument))
  rw [cohomological_upperHalfForm_slash cohomological weight vector rotation argument _
    (by rw [SpecialLinearGroup.det_mapGL]; rfl)]
  exact cuspUpperHalfForm_zero_at_infinity cusp weight (by exact_mod_cast weight_positive) vector _

def cuspPrincipalLowestSubmodule (cusp : CuspidalRepresentation) (weight : ℕ) : Submodule ℂ cusp.smooth where
  carrier := {vector | vector ∈ cuspFiniteFixedSubmodule cusp binaryPrincipalLevel ∧
    cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector ∧
    cuspLoweringOperator cusp vector = 0}
  zero_mem' := ⟨Submodule.zero_mem _, by simp, by simp⟩
  add_mem' {first second} first_member second_member := by
    refine ⟨Submodule.add_mem _ first_member.1 second_member.1, ?_, ?_⟩
    · rw [map_add, first_member.2.1, second_member.2.1, smul_add]
    · rw [map_add, first_member.2.2, second_member.2.2, add_zero]
  smul_mem' scalar vector member := by
    refine ⟨Submodule.smul_mem _ scalar member.1, ?_, ?_⟩
    · rw [map_smul, member.2.1, smul_comm]
    · rw [map_smul, member.2.2, smul_zero]

noncomputable def cuspPrincipalLowestForm {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℕ) (weight_positive : 0 < weight)
    (vector : cuspPrincipalLowestSubmodule cusp weight) : CuspForm binaryRealPrincipalLevel (weight : ℤ) where
  toFun := cuspUpperHalfForm cusp weight vector.val 1
  slash_action_eq' matrix member :=
    cohomological_principal_upperHalfForm_slash cohomological weight ⟨vector.val, vector.property.1⟩
      vector.property.2.1 matrix member
  holo' := cohomological_upperHalfForm_mdifferentiable cohomological weight vector.val
    (by simpa only [Complex.ofReal_natCast] using vector.property.2.1) vector.property.2.2 1
  zero_at_cusps' is_cusp :=
    cohomological_upperHalfForm_zero_at_cusp cohomological weight weight_positive vector.val
      vector.property.2.1 1 _ is_cusp

theorem cuspPrincipalLowestForm_apply {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℕ) (weight_positive : 0 < weight)
    (vector : cuspPrincipalLowestSubmodule cusp weight) (point : UpperHalfPlane) :
    cuspPrincipalLowestForm cohomological weight weight_positive vector point =
      cuspUpperHalfForm cusp weight vector.val 1 point := rfl

noncomputable def cuspPrincipalLowestFormLinear {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℕ) (weight_positive : 0 < weight) :
    cuspPrincipalLowestSubmodule cusp weight →ₗ[ℂ] CuspForm binaryRealPrincipalLevel (weight : ℤ) where
  toFun := cuspPrincipalLowestForm cohomological weight weight_positive
  map_add' first second := by
    apply DFunLike.ext
    intro point
    simp only [cuspPrincipalLowestForm_apply, cuspUpperHalfForm, cuspHolomorphicFunction,
      cuspUpperHalfOrbit_apply, Submodule.coe_add, map_add, Pi.add_apply, smul_add, _root_.add_apply]
  map_smul' scalar vector := by
    apply DFunLike.ext
    intro point
    simp only [cuspPrincipalLowestForm_apply, cuspUpperHalfForm, cuspHolomorphicFunction,
      cuspUpperHalfOrbit_apply, Submodule.coe_smul, map_smul, Pi.smul_apply, _root_.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
