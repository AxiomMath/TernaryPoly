module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.OrbitSmooth
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.GlobalScalar

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevBounds

theorem orbitDerivative_same_integralReduction {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (first second : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL)
    (sameReduction : Matrix.GeneralLinearGroup.map integralReduction first =
      Matrix.GeneralLinearGroup.map integralReduction second)
    (realMatrix : RealGL3) (order : ℕ) :
    orbitDerivative data.cusp order
        (planeCuspVector inducedSection
          (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding first) * atInfinity realMatrix)).val =
      orbitDerivative data.cusp order
        (planeCuspVector inducedSection
          (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding second) * atInfinity realMatrix)).val := by
  apply congrArg (fun vector : data.cusp.smooth => orbitDerivative data.cusp order vector.val)
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute]
  exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.planeCuspVector_same_integralReduction inducedSection
    (atInfinity realMatrix) first second sameReduction

theorem orbitDerivative_integral_compact_bound {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction) (order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ realMatrix : RealGL3,
      realMatrix.val.transpose * realMatrix.val = 1 →
      ∀ integralMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL,
        ‖orbitDerivative data.cusp order
          (planeCuspVector inducedSection
            (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding integralMatrix) *
              atInfinity realMatrix)).val‖ ≤ bound := by
  classical
  let residues := Set.range (Matrix.GeneralLinearGroup.map integralReduction (n := Fin 3))
  let : Fintype residues := Fintype.ofFinite residues
  have pointwiseBounds (residue : residues) := orbitDerivative_cuspVector_bound_on_compact inducedSection
    (Matrix.GeneralLinearGroup.map integralEmbedding
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.integralResidueRepresentative residue)) order
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Compact.isCompact_orthogonal
  choose bounds nonnegativeBounds boundProperty using pointwiseBounds
  refine ⟨∑ residue, bounds residue,
    Finset.sum_nonneg (fun residue _ => nonnegativeBounds residue),
    fun realMatrix orthogonality integralMatrix => ?_⟩
  let residue : residues :=
    ⟨Matrix.GeneralLinearGroup.map integralReduction integralMatrix, integralMatrix, rfl⟩
  rw [← orbitDerivative_same_integralReduction inducedSection
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.integralResidueRepresentative residue) integralMatrix
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.integralResidueRepresentative_reduction residue)]
  exact (boundProperty residue realMatrix orthogonality).trans
    (Finset.single_le_sum (fun residue _ => nonnegativeBounds residue) (Finset.mem_univ residue))

theorem orbitDerivative_maximalCompact_bound {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction) (order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ compactElement : AdelicGL,
      inMaximalCompact compactElement →
      ‖orbitDerivative data.cusp order (planeCuspVector inducedSection compactElement).val‖ ≤ bound := by
  obtain ⟨bound, nonnegativeBound, boundProperty⟩ := orbitDerivative_integral_compact_bound inducedSection order
  refine ⟨bound, nonnegativeBound, fun compactElement compactness => ?_⟩
  obtain ⟨integralMatrix, finiteEquality⟩ := compactness.2
  have estimate := boundProperty (realGroup compactElement) compactness.1 integralMatrix
  rw [finiteEquality, TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute,
    ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adelicGL_eq_mul] at estimate
  exact estimate

noncomputable def orbitSobolevNorm (data : CuspidalRepresentation) (order : ℕ) (vector : data.H) : ℝ :=
  ∑ derivativeOrder ∈ Finset.range (order + 1), ‖orbitDerivative data derivativeOrder vector‖

theorem norm_orbitDerivative_zero (data : CuspidalRepresentation) (vector : data.H) :
    ‖orbitDerivative data 0 vector‖ = ‖vector‖ := by
  have derivativeEquality := norm_iteratedFDeriv_zero (𝕜 := ℝ)
    (f := fun matrix : BinaryMatrix => data.π (atInfinity (invertibleMatrix matrix)) vector)
    (x := (1 : BinaryMatrix))
  have identityMatrix : invertibleMatrix (1 : BinaryMatrix) = 1 :=
    invertibleMatrix_units (1 : BinaryRealGL)
  rw [identityMatrix, TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth.atInfinity_one, map_one, Module.End.one_apply]
    at derivativeEquality
  exact derivativeEquality

theorem orbitSobolevNorm_nonneg (data : CuspidalRepresentation) (order : ℕ) (vector : data.H) :
    0 ≤ orbitSobolevNorm data order vector := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem norm_le_orbitSobolevNorm (data : CuspidalRepresentation) (order : ℕ) (vector : data.H) :
    ‖vector‖ ≤ orbitSobolevNorm data order vector := by
  rw [← norm_orbitDerivative_zero data vector]
  exact Finset.single_le_sum (f := fun derivativeOrder => ‖orbitDerivative data derivativeOrder vector‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.succ_pos order))

theorem orbitSobolevNorm_maximalCompact_bound {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction) (order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ compactElement : AdelicGL,
      inMaximalCompact compactElement →
      orbitSobolevNorm data.cusp order (planeCuspVector inducedSection compactElement).val ≤ bound := by
  choose bounds nonnegativeBounds boundProperty using orbitDerivative_maximalCompact_bound inducedSection
  refine ⟨∑ derivativeOrder ∈ Finset.range (order + 1), bounds derivativeOrder,
    Finset.sum_nonneg (fun derivativeOrder _ => nonnegativeBounds derivativeOrder), ?_⟩
  intro compactElement compactness
  exact Finset.sum_le_sum (fun derivativeOrder _ => boundProperty derivativeOrder compactElement compactness)

theorem compact_bound_of_sobolev_estimate {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ} (flatSection : IsFlatSection data sectionFamily)
    (order : ℕ) (constant : ℝ) (nonnegativeConstant : 0 ≤ constant)
    (sobolevEstimate : ∀ vector : data.cusp.smooth,
      vector.val ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data.cusp TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.finiteCongruence →
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm vector ≤ constant * orbitSobolevNorm data.cusp order vector.val) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ compactElement : AdelicGL, inMaximalCompact compactElement →
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm
        (planeCuspVector (flatSection.1 cohomologicalPoint) compactElement) ≤ bound := by
  obtain ⟨bound, nonnegativeBound, boundProperty⟩ :=
    orbitSobolevNorm_maximalCompact_bound (flatSection.1 cohomologicalPoint) order
  refine ⟨constant * bound, mul_nonneg nonnegativeConstant nonnegativeBound, ?_⟩
  intro compactElement compactness
  exact (sobolevEstimate _ (TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.cuspVector_mem_fixedSubspace
    (flatSection.1 cohomologicalPoint) compactElement compactness)).trans
      (mul_le_mul_of_nonneg_left (boundProperty compactElement compactness) nonnegativeConstant)

theorem hasSum_of_sobolev_estimate {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ} (flatSection : IsFlatSection data sectionFamily)
    (order : ℕ) (constant : ℝ) (nonnegativeConstant : 0 ≤ constant)
    (sobolevEstimate : ∀ vector : data.cusp.smooth,
      vector.val ∈ TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace data.cusp TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.finiteCongruence →
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm.cuspSupNorm vector ≤ constant * orbitSobolevNorm data.cusp order vector.val)
    (basePoint : AdelicGL) (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    HasSum (eisensteinSummand sectionFamily parameter basePoint)
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.literalSum sectionFamily parameter basePoint) := by
  obtain ⟨bound, nonnegativeBound, boundProperty⟩ :=
    compact_bound_of_sobolev_estimate flatSection order constant nonnegativeConstant sobolevEstimate
  exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalScalar.hasSum_of_compact_bound flatSection bound nonnegativeBound boundProperty
    basePoint parameter rightHalfPlane

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevBounds
