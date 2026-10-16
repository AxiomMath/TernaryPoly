module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.AnalyticSegmentDerivative
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.LocalScalarBound

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def cuspRealUnitaryEquiv (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL) :
    cusp.H ≃ₗᵢ[ℝ] cusp.H where
  toLinearEquiv :=
    { toLinearMap := (cusp.π matrix).restrictScalars ℝ
      invFun := cusp.π matrix⁻¹
      left_inv := by
        intro vector
        change cusp.π matrix⁻¹ (cusp.π matrix vector) = vector
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      right_inv := by
        intro vector
        change cusp.π matrix (cusp.π matrix⁻¹ vector) = vector
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] }
  norm_map' := cusp.unitary matrix

theorem cusp_segmentDerivativeAverage_orbit
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (cusp : CuspidalRepresentation) (family : D → cusp.H)
    (center displacement direction : D) (matrix : Matrix (Fin 2) (Fin 2) ℝ) :
    cuspCenteredMatrixOrbit cusp (segmentDerivativeAverage family center displacement direction) matrix =
      segmentDerivativeAverage (fun point => cuspCenteredMatrixOrbit cusp (family point) matrix) center displacement direction :=
  (segmentDerivativeAverage_comp_isometry
    (cuspRealUnitaryEquiv cusp (atInfinity (invertibleMatrix (1 + matrix)))) family center displacement direction).symm

theorem cusp_segmentDerivativeAverage_fixed
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (cusp : CuspidalRepresentation) (family : D → cuspFiniteFixedSubmodule cusp binaryPrincipalLevel)
    (center displacement direction : D) :
    segmentDerivativeAverage (fun point => (family point).val.val) center displacement direction ∈
      cuspHilbertFiniteFixedSubmodule cusp binaryPrincipalLevel := by
  intro finite
  have commute := segmentDerivativeAverage_comp_isometry
    (cuspRealUnitaryEquiv cusp (atFinite finite.val)) (fun point => (family point).val.val) center displacement direction
  change _ = cusp.π (atFinite finite.val) _ at commute
  rw [← commute]
  congr 1
  funext point
  exact (family point).property finite

theorem cusp_family_segment_scalar_bound
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [ProperSpace D]
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (family : D → cuspFiniteFixedSubmodule cusp binaryPrincipalLevel) (center : D)
    (analytic : AnalyticAt ℝ
      (fun input : Matrix (Fin 2) (Fin 2) ℝ × D =>
        cuspCenteredMatrixOrbit cusp (family input.2).val.val input.1) (0, center)) :
    ∃ lifted : (D × D) → cuspFiniteFixedSubmodule cusp binaryPrincipalLevel,
      (∀ᶠ pair in nhds 0, (lifted pair).val.val =
        segmentDerivativeAverage (fun point => (family point).val.val) center pair.1 pair.2) ∧
      ∃ bound : ℝ, 0 ≤ bound ∧ ∀ᶠ pair in nhds 0,
        ‖cuspBoundedRealization cusp (lifted pair).val‖ ≤ bound := by
  classical
  let average (pair : D × D) := segmentDerivativeAverage (fun point => (family point).val.val) center pair.1 pair.2
  have orbit_analytic : AnalyticAt ℝ
      (fun input : Matrix (Fin 2) (Fin 2) ℝ × (D × D) =>
        cuspCenteredMatrixOrbit cusp (average input.2) input.1) 0 := by
    simpa only [average, cusp_segmentDerivativeAverage_orbit] using analyticAt_segmentDerivativeAverage analytic
  have smooth_near : ∀ᶠ pair : D × D in nhds 0, average pair ∈ cusp.smooth := by
    have near := orbit_analytic.eventually_analyticAt
    have pulled := (continuous_const.prodMk continuous_id).continuousAt near
    filter_upwards [pulled] with pair analytic_at
    apply (cusp.smooth_exact _).mpr
    refine ⟨cuspRealOrbit_smooth_of_centered cusp _ ?_, binaryPrincipalLevel,
      binaryPrincipalLevel_isOpen, binaryPrincipalLevel_isCompact, cusp_segmentDerivativeAverage_fixed cusp family center pair.1 pair.2⟩
    exact analytic_at.comp (f := fun matrix : Matrix (Fin 2) (Fin 2) ℝ => (matrix, pair))
      (x := 0) (analyticAt_id.prod analyticAt_const)
  let lifted (pair : D × D) : cuspFiniteFixedSubmodule cusp binaryPrincipalLevel :=
    if smooth : average pair ∈ cusp.smooth then
      ⟨⟨average pair, smooth⟩, cusp_segmentDerivativeAverage_fixed cusp family center pair.1 pair.2⟩ else 0
  have equality : ∀ᶠ pair in nhds 0, (lifted pair).val.val = average pair := by
    filter_upwards [smooth_near] with pair smooth
    simp only [lifted, dite_eq_left smooth]
  refine ⟨lifted, equality, ?_⟩
  apply cusp_family_local_scalar_bound cohomological lifted 0
  apply orbit_analytic.congr
  have near := (continuous_snd.continuousAt (x := (0 : Matrix (Fin 2) (Fin 2) ℝ × (D × D)))) equality
  filter_upwards [near] with input same
  exact congrArg (fun vector => cuspCenteredMatrixOrbit cusp vector input.1) same.symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
