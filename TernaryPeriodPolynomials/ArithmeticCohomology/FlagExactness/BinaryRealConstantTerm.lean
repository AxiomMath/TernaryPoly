module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.PlaneConstantTerm
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.Periodicity

@[expose] public section


/-!
# Real constant terms of plane-induced sections along the Levi unipotent

Plane-induced sections have vanishing adelic constant term along the unipotent of
the `GL₂` Levi (`induced_binary_unipotent_cuspidal`). If, moreover, the integrand is
invariant under the finite lattice `M·Ẑ`, this constant term is a real integral over
`[0,1)` of the real translates by `n(M t)`, and that real integral vanishes.

This is the analytic input to constant-term averaging in the flag-exactness
obligation of `general_eisenstein_graph`.

Original work (AxiomDeep, Claude Opus 5.5). It uses the measure infrastructure of
`Proofs/EisensteinRegularization`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.FlagExactness

/-- One-dimensional rational scaling of rationally periodic integrals over the
additive fundamental domain. -/
theorem adele_periodic_integral_rational_scaling (function : Adeles → ℂ)
    (periodic : ∀ rational : ℚ, ∀ value, function (rationalAdele rational + value) = function value)
    (scalar : ℚˣ) :
    (∫ value in additiveDomain, function (rationalAdele scalar.val * value) ∂adeleMeasure) =
      ∫ value in additiveDomain, function value ∂adeleMeasure := by
  have plane := radical_periodic_integral_rational_scaling (fun point => function point.1)
    (fun rational point => periodic rational.1 point.1) scalar
  have hone : (adeleMeasure.restrict additiveDomain).real Set.univ = 1 := by
    simp [Measure.real]
  have lhs : (∫ point : Adeles × Adeles,
      function (rationalAdele scalar.val * point.1) ∂planeDomainMeasure) =
      ∫ value in additiveDomain, function (rationalAdele scalar.val * value) ∂adeleMeasure := by
    rw [planeDomainMeasure]
    exact (integral_fun_fst (fun value => function (rationalAdele scalar.val * value))).trans
      (by rw [hone, one_smul])
  have rhs : (∫ point : Adeles × Adeles, function point.1 ∂planeDomainMeasure) =
      ∫ value in additiveDomain, function value ∂adeleMeasure := by
    rw [planeDomainMeasure]
    exact (integral_fun_fst function).trans (by rw [hone, one_smul])
  rw [← lhs, ← rhs]
  exact plane

/-- The real constant term along `n(M t)` vanishes once the integrand is `M·Ẑ`-invariant. -/
theorem induced_binary_real_constant_term {degree : ℕ} {inducingData : InducingData degree}
    {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue)
    (groupElement : AdelicGL) (M : ℕ) (positive : 0 < M)
    (finiteInvariant : ∀ (t : ℝ) (z : FiniteAdeles), z ∈ Set.range integralEmbedding →
      sectionValue (planeLevi (binaryUnipotent ((t, (M : FiniteAdeles) * z) : Adeles)) 1 * groupElement) =
        sectionValue (planeLevi (binaryUnipotent ((t, 0) : Adeles)) 1 * groupElement))
    (measurable : Measurable (fun t : ℝ =>
      sectionValue (planeLevi (binaryUnipotent ((t, 0) : Adeles)) 1 * groupElement))) :
    (∫ t in Set.Ico (0 : ℝ) 1,
      sectionValue (planeLevi (binaryUnipotent ((((M : ℝ) * t), 0) : Adeles)) 1 * groupElement)) = 0 := by
  set F : ℝ → ℂ := fun t =>
    sectionValue (planeLevi (binaryUnipotent ((t, 0) : Adeles)) 1 * groupElement)
  have cusp := (induced_binary_unipotent_cuspidal induced groupElement).2
  have scaled := adele_periodic_integral_rational_scaling
    (fun coordinate => sectionValue (planeLevi (binaryUnipotent coordinate) 1 * groupElement))
    (induced_binary_unipotent_periodic induced groupElement) (Units.mk0 (M : ℚ) (by exact_mod_cast positive.ne'))
  rw [cusp] at scaled
  -- on the domain the scaled integrand depends only on the real coordinate
  have measurable_domain : MeasurableSet additiveDomain :=
    measurableSet_Ico.prod integralLattice_isCompact.measurableSet
  have pointwise : ∀ value ∈ additiveDomain,
      sectionValue (planeLevi (binaryUnipotent
        (rationalAdele (Units.mk0 (M : ℚ) (by exact_mod_cast positive.ne')).val * value)) 1 * groupElement) =
      F ((M : ℝ) * value.1) := by
    intro value member
    have hvalue : rationalAdele (Units.mk0 (M : ℚ) (by exact_mod_cast positive.ne')).val * value =
        (((M : ℝ) * value.1, (M : FiniteAdeles) * value.2) : Adeles) := by
      apply Prod.ext
      · simp
      · simp
    rw [hvalue]
    exact finiteInvariant _ value.2 member.2
  have hcongr : (∫ value in additiveDomain, sectionValue (planeLevi (binaryUnipotent
        (rationalAdele (Units.mk0 (M : ℚ) (by exact_mod_cast positive.ne')).val * value)) 1 * groupElement)
          ∂adeleMeasure) =
      ∫ value in additiveDomain, F ((M : ℝ) * value.1) ∂adeleMeasure :=
    setIntegral_congr_fun measurable_domain pointwise
  rw [hcongr] at scaled
  have hmeas : Measurable (fun t : ℝ => F ((M : ℝ) * t)) :=
    measurable.comp (measurable_const.mul measurable_id)
  have projection := integral_map additiveDomain_real_projection.measurable.aemeasurable
    (hmeas.aestronglyMeasurable (μ := Measure.map (Prod.fst : Adeles → ℝ)
      (adeleMeasure.restrict additiveDomain)))
  rw [additiveDomain_real_projection.map_eq] at projection
  rw [← projection] at scaled
  exact scaled
end TernaryPeriodPolynomials.FlagExactness
