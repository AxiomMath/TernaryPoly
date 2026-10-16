module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Gamma.OneThreeSmallWeight
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.IntegerRealization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cuspUpperHalfForm_integral_fixed (cusp : CuspidalRepresentation) (weight : ℝ)
    (vector : cusp.smooth) (matrix : SpecialLinearGroup (Fin 2) ℤ)
    (fixed : cuspSmoothAction cusp (atFinite (SpecialLinearGroup.mapGL FiniteAdeles matrix)) vector = vector) :
    cuspUpperHalfForm cusp weight vector (atInfinity (SpecialLinearGroup.mapGL ℝ matrix)) =
      cuspUpperHalfForm cusp weight vector 1 := by
  funext point
  simp only [cuspUpperHalfForm, cuspHolomorphicFunction, cuspUpperHalfOrbit_apply, one_mul,
    cusp_realize_integral_translation cusp vector matrix fixed]

noncomputable def cuspGammaOneThreeLowestForm
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (weight : ℕ) (weight_positive : 0 < weight) (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (lowering : cuspLoweringOperator cusp vector = 0)
    (fixed : ∀ matrix ∈ CongruenceSubgroup.Gamma1 3,
      cuspSmoothAction cusp (atFinite (SpecialLinearGroup.mapGL FiniteAdeles matrix)) vector = vector) :
    CuspForm binaryRealGammaOneThree (weight : ℤ) where
  toFun := cuspUpperHalfForm cusp weight vector 1
  slash_action_eq' matrix member := by
    obtain ⟨integralMatrix, integral_member, rfl⟩ := member
    rw [cohomological_upperHalfForm_slash cohomological weight vector rotation 1 _
      (by rw [SpecialLinearGroup.det_mapGL]; rfl), one_mul]
    exact cuspUpperHalfForm_integral_fixed cusp weight vector integralMatrix (fixed _ integral_member)
  holo' := cohomological_upperHalfForm_mdifferentiable cohomological weight vector
    (by simpa only [Complex.ofReal_natCast] using rotation) lowering 1
  zero_at_cusps' is_cusp := by
    have included : binaryRealGammaOneThree ≤
        (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range := by
      rintro matrix ⟨integralMatrix, _, equality⟩
      exact ⟨integralMatrix, equality⟩
    apply (OnePoint.isZeroAt_iff_forall_SL2Z (is_cusp.mono included)).mpr
    intro matrix _
    change UpperHalfPlane.IsZeroAtImInfty (SlashAction.map (weight : ℤ)
      (SpecialLinearGroup.mapGL ℝ matrix) (cuspUpperHalfForm cusp weight vector 1))
    rw [cohomological_upperHalfForm_slash cohomological weight vector rotation 1 _
      (by rw [SpecialLinearGroup.det_mapGL]; rfl)]
    exact cuspUpperHalfForm_zero_at_infinity cusp weight (by exact_mod_cast weight_positive) vector _

theorem cuspPrincipalLowest_zero_of_gammaOneThree_fixed
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (weight : ℕ) (weight_positive : 0 < weight) (weight_small : weight < 6)
    (vector : cuspPrincipalLowestSubmodule cusp weight)
    (fixed : ∀ matrix ∈ CongruenceSubgroup.Gamma1 3,
      cuspSmoothAction cusp (atFinite (SpecialLinearGroup.mapGL FiniteAdeles matrix)) vector.val = vector.val)
    (reflection_fixed : cuspSmoothAction cusp
      (atFinite (GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) binaryIntegralRowReflection)) vector.val = vector.val) :
    vector = 0 := by
  have form_zero := gammaOneThree_cusp_eq_zero_of_weight_lt_six (by exact_mod_cast weight_small)
    (cuspGammaOneThreeLowestForm cohomological weight weight_positive vector.val
      vector.property.2.1 vector.property.2.2 fixed)
  have upper_zero : cuspUpperHalfForm cusp weight vector.val 1 = 0 :=
    congrArg (fun form : CuspForm binaryRealGammaOneThree (weight : ℤ) => (form : UpperHalfPlane → ℂ)) form_zero
  apply cuspPrincipalLowest_zero_of_real_slice cohomological weight weight_positive vector
  exact cohomological_realize_zero_all_real_of_reflection_fixed cohomological weight vector.val
    vector.property.2.1 upper_zero reflection_fixed

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
