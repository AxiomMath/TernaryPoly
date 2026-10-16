module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Induced.AnalyticFamilies

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedAnalyticFamilies
open scoped Matrix.Norms.Elementwise NNReal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticScalar

def ContinuousStages (data : CuspidalRepresentation) : Prop :=
  ∀ radius : ℝ≥0, ∀ positiveRadius : 0 < radius,
    Continuous (TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticRealization.stageRealization data finiteCongruence
      finiteCongruence_isOpen finiteCongruence_isCompact radius positiveRadius)

theorem real_compact_bound {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (stageContinuity : ContinuousStages data.cusp)
    (finiteMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL)
    {compactSet : Set RealGL3} (compactness : IsCompact compactSet) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ realMatrix ∈ compactSet,
      cuspSupNorm (matrixCuspVector inducedSection finiteMatrix realMatrix.val) ≤ bound := by
  obtain ⟨bound, boundProperty⟩ := compactness.exists_bound_of_continuousOn
    (realCuspSupNorm_continuous_of_stage_continuity inducedSection stageContinuity finiteMatrix).continuousOn
  refine ⟨max 0 bound, le_max_left _ _, ?_⟩
  intro realMatrix membership
  have normEquality := Real.norm_of_nonneg
    (cuspSupNorm_nonneg (matrixCuspVector inducedSection finiteMatrix realMatrix.val))
  exact normEquality.symm.le.trans ((boundProperty realMatrix membership).trans (le_max_right _ _))

theorem matrixCuspVector_same_reduction {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (first second : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL)
    (sameReduction : Matrix.GeneralLinearGroup.map integralReduction first =
      Matrix.GeneralLinearGroup.map integralReduction second) (matrix : PlaneMatrix) :
    matrixCuspVector inducedSection first matrix = matrixCuspVector inducedSection second matrix := by
  unfold matrixCuspVector
  simp only [TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute]
  exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.planeCuspVector_same_integralReduction inducedSection
    (atInfinity (invertibleMatrix matrix)) first second sameReduction

theorem integral_compact_bound {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (stageContinuity : ContinuousStages data.cusp) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ realMatrix : RealGL3,
      realMatrix.val.transpose * realMatrix.val = 1 →
      ∀ finiteMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL,
        cuspSupNorm (matrixCuspVector inducedSection finiteMatrix realMatrix.val) ≤ bound := by
  classical
  let residues := Set.range (Matrix.GeneralLinearGroup.map integralReduction (n := Fin 3))
  let _ : Fintype residues := Fintype.ofFinite residues
  have pointwiseBounds (residue : residues) := real_compact_bound inducedSection stageContinuity
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.integralResidueRepresentative residue) TernaryPeriodPolynomials.PlaneEisensteinContinuation.Compact.isCompact_orthogonal
  choose bounds nonnegativeBounds boundProperty using pointwiseBounds
  refine ⟨∑ residue, bounds residue, Finset.sum_nonneg (fun residue _ => nonnegativeBounds residue), ?_⟩
  intro realMatrix orthogonality finiteMatrix
  let residue : residues :=
    ⟨Matrix.GeneralLinearGroup.map integralReduction finiteMatrix, finiteMatrix, rfl⟩
  have vectorEquality := matrixCuspVector_same_reduction inducedSection
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.integralResidueRepresentative residue) finiteMatrix
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.integralResidueRepresentative_reduction residue) realMatrix.val
  exact (congrArg cuspSupNorm vectorEquality).symm.le.trans
    ((boundProperty residue realMatrix orthogonality).trans
      (Finset.single_le_sum (fun residue _ => nonnegativeBounds residue) (Finset.mem_univ residue)))

theorem maximalCompact_bound {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (stageContinuity : ContinuousStages data.cusp) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ compactElement : AdelicGL, inMaximalCompact compactElement →
      cuspSupNorm (planeCuspVector inducedSection compactElement) ≤ bound := by
  obtain ⟨bound, nonnegativeBound, boundProperty⟩ := integral_compact_bound inducedSection stageContinuity
  refine ⟨bound, nonnegativeBound, ?_⟩
  intro compactElement compactness
  obtain ⟨finiteMatrix, finiteEquality⟩ := compactness.2
  have vectorEquality : matrixCuspVector inducedSection finiteMatrix (realGroup compactElement).val =
      planeCuspVector inducedSection compactElement := by
    unfold matrixCuspVector
    rw [invertibleMatrix_units, finiteEquality, TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute,
      ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adelicGL_eq_mul]
  exact (congrArg cuspSupNorm vectorEquality).symm.le.trans
    (boundProperty (realGroup compactElement) compactness.1 finiteMatrix)

theorem hasSum_of_stage_continuity {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ}
    (flatSection : IsFlatSection data sectionFamily)
    (stageContinuity : ContinuousStages data.cusp)
    (basePoint : AdelicGL) (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    HasSum (eisensteinSummand sectionFamily parameter basePoint)
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.literalSum sectionFamily parameter basePoint) := by
  obtain ⟨bound, nonnegativeBound, compactBound⟩ := maximalCompact_bound (flatSection.1 cohomologicalPoint) stageContinuity
  exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalScalar.hasSum_of_compact_bound flatSection bound nonnegativeBound compactBound
    basePoint parameter rightHalfPlane

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticScalar
