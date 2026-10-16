module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Radical.PeriodicScaling
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Plane.PrincipalPeriod
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Boundary.ResidueConstantTerms
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Boundary.ResidueMeasurable

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def realPlaneUnitMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Set.Ico 0 1)).prod (volume.restrict (Set.Ico 0 1))

instance realPlaneUnitMeasure_probability : IsProbabilityMeasure realPlaneUnitMeasure := by
  constructor
  rw [realPlaneUnitMeasure, ← Set.univ_prod_univ, Measure.prod_prod]
  norm_num

theorem additiveDomain_real_projection :
    MeasurePreserving (Prod.fst : Adeles → ℝ) (adeleMeasure.restrict additiveDomain)
      (volume.restrict (Set.Ico 0 1)) := by
  refine ⟨measurable_fst, ?_⟩
  rw [adeleMeasure, additiveDomain, ← Measure.prod_restrict, Measure.map_fst_prod,
    Measure.restrict_apply_univ, finiteMeasure_integralLattice, one_smul]

theorem planeDomain_real_projection :
    MeasurePreserving (fun point : Adeles × Adeles => (point.1.1, point.2.1))
      planeDomainMeasure realPlaneUnitMeasure :=
  additiveDomain_real_projection.prod additiveDomain_real_projection

theorem planeDomain_integral_real_projection {function : ℝ × ℝ → ℂ}
    (measurable : Measurable function) :
    (∫ point : Adeles × Adeles, function (point.1.1, point.2.1) ∂planeDomainMeasure) =
      ∫ point, function point ∂realPlaneUnitMeasure := by
  have equality := integral_map planeDomain_real_projection.measurable.aemeasurable
    (measurable.aestronglyMeasurable (μ := Measure.map
      (fun point : Adeles × Adeles => (point.1.1, point.2.1)) planeDomainMeasure))
  rw [planeDomain_real_projection.map_eq] at equality
  exact equality.symm

theorem normalizedBoundaryResidue_plane_rational_periodic
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (matrix : AdelicGL) (rational : ℚ × ℚ) (point : Adeles × Adeles) :
    normalizedBoundaryResidue degree continuation
      (planeUnipotent (rationalAdele rational.1 + point.1) (rationalAdele rational.2 + point.2) * matrix) =
      normalizedBoundaryResidue degree continuation (planeUnipotent point.1 point.2 * matrix) := by
  rw [planeUnipotent_add, mul_assoc, ← map_planeUnipotent]
  exact normalizedBoundaryResidue_rational_invariant flat continuation_spec
    (planeUnipotent rational.1 rational.2) _

theorem normalizedBoundaryResidue_real_plane_constant_term_zero
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) (matrix : AdelicGL)
    (finite_eq : finiteGroup matrix = GeneralLinearGroup.map integralEmbedding integral) :
    (∫ point : ℝ × ℝ, normalizedBoundaryResidue degree continuation
      (atInfinity (planeUnipotent (3 * point.1) (3 * point.2)) * matrix) ∂realPlaneUnitMeasure) = 0 := by
  have continuous_map : Continuous (fun point : ℝ × ℝ =>
      atInfinity (planeUnipotent (3 * point.1) (3 * point.2)) * matrix) := by
    simp only [atInfinity_planeUnipotent]
    exact (planeUnipotent_continuous.comp
      (((continuous_const.mul continuous_fst).prodMk continuous_const).prodMk
        ((continuous_const.mul continuous_snd).prodMk continuous_const))).mul continuous_const
  rw [← planeDomain_integral_real_projection
    (normalizedBoundaryResidue_measurable flat continuation_spec continuous_map)]
  have scaled := radical_periodic_integral_rational_scaling
    (fun point : Adeles × Adeles => normalizedBoundaryResidue degree continuation
      (planeUnipotent point.1 point.2 * matrix))
    (normalizedBoundaryResidue_plane_rational_periodic flat continuation_spec matrix)
    (Units.mk0 (3 : ℚ) (by norm_num))
  simp only [Units.val_mk0, map_ofNat] at scaled
  rw [← normalizedBoundaryResidue_plane_constant_term_zero flat continuation_spec matrix, ← scaled]
  apply integral_congr_ae
  rw [planeDomainMeasure_eq]
  have measurable_domain : MeasurableSet additiveDomain :=
    measurableSet_Ico.prod integralLattice_isCompact.measurableSet
  filter_upwards [ae_restrict_mem (measurable_domain.prod measurable_domain)] with point member
  exact (normalizedBoundaryResidue_plane_three_finite_removal flat continuation_spec integral matrix
    finite_eq point.1 point.2 member.1.2 member.2.2).symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
