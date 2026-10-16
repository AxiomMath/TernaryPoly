module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.Decomposition

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalHeight

noncomputable def parabolicPart (matrix : AdelicGL) : planeParabolic Adeles :=
  Classical.choose (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteDecomposition.adelic_plane_compact_factorization matrix)

noncomputable def compactPart (matrix : AdelicGL) : AdelicGL :=
  Classical.choose (Classical.choose_spec
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteDecomposition.adelic_plane_compact_factorization matrix))

theorem parabolicPart_mul_compactPart (matrix : AdelicGL) :
    matrix = (parabolicPart matrix).val * compactPart matrix :=
  (Classical.choose_spec (Classical.choose_spec
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteDecomposition.adelic_plane_compact_factorization matrix))).1

theorem compactPart_mem (matrix : AdelicGL) : inMaximalCompact (compactPart matrix) :=
  (Classical.choose_spec (Classical.choose_spec
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteDecomposition.adelic_plane_compact_factorization matrix))).2

noncomputable def height (matrix : AdelicGL) : ℝ := planeHeightLog (parabolicPart matrix)

theorem flatSection_parameter {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (matrix : AdelicGL) (parameter : ℂ) :
    sectionFamily parameter matrix =
      Complex.exp ((parameter - cohomologicalPoint) * (height matrix : ℂ)) *
        sectionFamily cohomologicalPoint matrix := by
  have formula := flatSection_planeParabolic_exp flatSection
    (parabolicPart matrix) (compactPart matrix) (compactPart_mem matrix) parameter
  rw [← parabolicPart_mul_compactPart] at formula
  exact formula

theorem flatSection_change_parameter {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (matrix : AdelicGL)
    (parameter reference : ℂ) :
    sectionFamily parameter matrix =
      Complex.exp ((parameter - reference) * (height matrix : ℂ)) *
        sectionFamily reference matrix := by
  rw [flatSection_parameter flatSection matrix parameter,
    flatSection_parameter flatSection matrix reference, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem eisensteinSummand_change_parameter {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) (basePoint : AdelicGL) (flag : Flags .plane)
    (parameter reference : ℂ) :
    eisensteinSummand sectionFamily parameter basePoint flag =
      Complex.exp ((parameter - reference) * (height (rationalGroup flag.out⁻¹ * basePoint) : ℂ)) *
        eisensteinSummand sectionFamily reference basePoint flag :=
  flatSection_change_parameter flatSection _ parameter reference

theorem flatSection_cuspVector_bound {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter : ℂ, ∀ matrix : AdelicGL,
      ‖(planeCuspVector (flatSection.1 parameter) matrix).val‖ ≤
        Real.exp ((-2 * inductionExponent .plane parameter).re *
            Real.log (adeleNorm (planeCornerUnit (parabolicPart matrix)) : ℝ) +
          (binaryInductionExponent degree .plane parameter).re *
            Real.log (adeleNorm
              (Matrix.GeneralLinearGroup.det (planeBinaryBlock (parabolicPart matrix))) : ℝ)) *
          bound := by
  obtain ⟨bound, nonnegativeBound, compactBound⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.flatSection_maximalCompact_cuspVector_bound flatSection
  refine ⟨bound, nonnegativeBound, fun parameter matrix => ?_⟩
  have formula := TernaryPeriodPolynomials.PlaneEisensteinContinuation.Bounds.norm_planeCuspVector_planeParabolic (flatSection.1 parameter)
    (parabolicPart matrix) (compactPart matrix)
  rw [← parabolicPart_mul_compactPart] at formula
  rw [formula]
  exact mul_le_mul_of_nonneg_left
    (compactBound parameter (compactPart matrix) (compactPart_mem matrix)) (Real.exp_pos _).le

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalHeight
