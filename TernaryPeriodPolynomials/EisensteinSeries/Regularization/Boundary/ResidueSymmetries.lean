module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Boundary.Residue
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.Symmetries

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalizedBoundaryResidue_continuation_tendsto
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) (matrix : AdelicGL) :
    Tendsto (fun displacement : ℝ => (displacement : ℂ) *
      unitaryNormalize degree continuation ((3 : ℂ) / 2 + (displacement : ℂ)) matrix)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (normalizedBoundaryResidue degree continuation matrix)) := by
  apply (normalizedBoundaryResidue_tendsto flat continuation_spec matrix).congr'
  filter_upwards [normalized_continuation_boundary_ray_eq_actual_sum flat continuation_spec matrix]
    with displacement same
  rw [same]

theorem normalizedBoundaryResidue_of_germ_symmetry
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (source target : AdelicGL) (multiplier : ℂ)
    (symmetry : (fun parameter => unitaryNormalize degree continuation parameter target) =ᶠ[
      nhdsWithin ((3 : ℂ) / 2) {((3 : ℂ) / 2)}ᶜ]
      (fun parameter => multiplier * unitaryNormalize degree continuation parameter source)) :
    normalizedBoundaryResidue degree continuation target = multiplier * normalizedBoundaryResidue degree continuation source := by
  apply tendsto_nhds_unique (normalizedBoundaryResidue_continuation_tendsto flat continuation_spec target)
  apply ((normalizedBoundaryResidue_continuation_tendsto flat continuation_spec source).const_mul multiplier).congr'
  filter_upwards [(positive_real_ray_tendsto ((3 : ℂ) / 2)).eventually symmetry] with displacement same
  rw [same]
  ring

theorem normalizedBoundaryResidue_rational_invariant
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (rationalMatrix : RationalGL3) (matrix : AdelicGL) :
    normalizedBoundaryResidue degree continuation (rationalGroup rationalMatrix * matrix) =
      normalizedBoundaryResidue degree continuation matrix := by
  simpa only [one_mul] using normalizedBoundaryResidue_of_germ_symmetry flat continuation_spec
    matrix (rationalGroup rationalMatrix * matrix) 1
    (by simpa only [one_mul] using unitaryNormalize_continuation_rational_germ flat continuation_spec rationalMatrix matrix ((3 : ℂ) / 2))

theorem normalizedBoundaryResidue_finite_level
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (level : finiteLevel) (matrix : AdelicGL) :
    normalizedBoundaryResidue degree continuation (matrix * atFinite level.val) =
      normalizedBoundaryResidue degree continuation matrix := by
  simpa only [one_mul] using normalizedBoundaryResidue_of_germ_symmetry flat continuation_spec
    matrix (matrix * atFinite level.val) 1
    (by simpa only [one_mul] using unitaryNormalize_continuation_finite_level_germ flat continuation_spec level matrix ((3 : ℂ) / 2))

theorem normalizedBoundaryResidue_central_character
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (idele : Adelesˣ) (matrix : AdelicGL) :
    normalizedBoundaryResidue degree continuation (GeneralLinearGroup.scalar (Fin 3) idele * matrix) =
      (inducingData.chi.toMonoidHom idele * inducingData.cusp.centralCharacter idele) *
        normalizedBoundaryResidue degree continuation matrix :=
  normalizedBoundaryResidue_of_germ_symmetry flat continuation_spec matrix _ _
    (unitaryNormalize_continuation_central_germ flat continuation_spec idele matrix ((3 : ℂ) / 2))

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
