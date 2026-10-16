module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Analytic.Scalar
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Baire.LocallyCompactRegular

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothBounds
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedAnalyticFamilies
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarLocalBounds

theorem smooth_continuous {size count : ℕ} {Target : Type}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    {function : (Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ) → Target}
    (smoothFunction : Smooth function) : Continuous function := by
  have continuity := smoothFunction.continuousOn.comp_continuous
    (continuous_pi (fun index => Units.continuous_val.comp (continuous_apply index)))
    (fun matrices index => Matrix.GeneralLinearGroup.det_ne_zero (matrices index))
  exact continuity.congr (matrixLift_at_units function)

theorem scalarEvaluation_continuous {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (basePoint : AdelicGL) (evaluationPoint : BinaryAdelicGL) :
    Continuous (fun realMatrix : RealGL3 =>
      data.cusp.realize (planeCuspVector inducedSection (basePoint * atInfinity realMatrix)) evaluationPoint) := by
  have continuity := (smooth_continuous (inducedSection.1 (planeLevi evaluationPoint 1 * basePoint))).comp
    (continuous_pi (fun _ : Fin 1 => continuous_id))
  simpa only [realize_planeCuspVector, mul_assoc, Function.comp_apply, id_eq] using continuity.const_mul
    (normPower (Matrix.GeneralLinearGroup.det evaluationPoint) (-binaryInductionExponent degree .plane parameter))

theorem realCuspSupNorm_lowerSemicontinuous {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (basePoint : AdelicGL) :
    LowerSemicontinuous (fun realMatrix : RealGL3 =>
      cuspSupNorm (planeCuspVector inducedSection (basePoint * atInfinity realMatrix))) := by
  have bound (realMatrix : RealGL3) : BddAbove (Set.range (fun evaluationPoint : BinaryAdelicGL =>
      ‖data.cusp.realize (planeCuspVector inducedSection (basePoint * atInfinity realMatrix)) evaluationPoint‖)) := by
    obtain ⟨constant, boundProperty⟩ := data.cusp.bounded
      (planeCuspVector inducedSection (basePoint * atInfinity realMatrix))
    exact ⟨constant, by rintro _ ⟨evaluationPoint, rfl⟩; exact boundProperty evaluationPoint⟩
  have semicontinuity := lowerSemicontinuous_ciSup bound (fun evaluationPoint =>
    (scalarEvaluation_continuous inducedSection basePoint evaluationPoint).norm.lowerSemicontinuous)
  have normEquality : (fun realMatrix : RealGL3 =>
      cuspSupNorm (planeCuspVector inducedSection (basePoint * atInfinity realMatrix))) =
      (fun realMatrix : RealGL3 => ⨆ evaluationPoint : BinaryAdelicGL,
        ‖data.cusp.realize (planeCuspVector inducedSection (basePoint * atInfinity realMatrix)) evaluationPoint‖) := by
    funext realMatrix
    exact lp.norm_eq_ciSup (boundedRealization data.cusp
      (planeCuspVector inducedSection (basePoint * atInfinity realMatrix)))
  rw [normEquality]
  exact semicontinuity

theorem matrixCuspSupNorm_lowerSemicontinuous {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (finiteMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL) :
    LowerSemicontinuous (fun realMatrix : RealGL3 =>
      cuspSupNorm (matrixCuspVector inducedSection finiteMatrix realMatrix.val)) := by
  simpa only [matrixCuspVector, TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth.invertibleMatrix_units] using
    realCuspSupNorm_lowerSemicontinuous inducedSection
      (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding finiteMatrix))

/-- At a fixed real point the integral finite factors have only finitely many possible values. -/
theorem integral_pointwise_bound {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction) (realMatrix : RealGL3) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ finiteMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL,
      cuspSupNorm (matrixCuspVector inducedSection finiteMatrix realMatrix.val) ≤ bound := by
  classical
  let residues := Set.range (Matrix.GeneralLinearGroup.map integralReduction (n := Fin 3))
  let _ : Fintype residues := Fintype.ofFinite residues
  let bounds (residue : residues) := cuspSupNorm (matrixCuspVector inducedSection
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.integralResidueRepresentative residue) realMatrix.val)
  have nonnegativeBounds (residue : residues) : 0 ≤ bounds residue := cuspSupNorm_nonneg _
  refine ⟨∑ residue, bounds residue, Finset.sum_nonneg (fun residue _ => nonnegativeBounds residue), ?_⟩
  intro finiteMatrix
  let residue : residues :=
    ⟨Matrix.GeneralLinearGroup.map integralReduction finiteMatrix, finiteMatrix, rfl⟩
  have vectorEquality := TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticScalar.matrixCuspVector_same_reduction inducedSection
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.integralResidueRepresentative residue) finiteMatrix
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.integralResidueRepresentative_reduction residue) realMatrix.val
  exact (congrArg cuspSupNorm vectorEquality).symm.le.trans
    (Finset.single_le_sum (fun residue _ => nonnegativeBounds residue) (Finset.mem_univ residue))

def integralBoundSet {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction) (bound : ℕ) : Set RealGL3 :=
  {realMatrix | ∀ finiteMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL,
    cuspSupNorm (matrixCuspVector inducedSection finiteMatrix realMatrix.val) ≤ bound}

theorem integralBoundSet_isClosed {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction) (bound : ℕ) :
    IsClosed (integralBoundSet inducedSection bound) := by
  have equality : integralBoundSet inducedSection bound =
      ⋂ finiteMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL,
        (fun realMatrix : RealGL3 => cuspSupNorm (matrixCuspVector inducedSection finiteMatrix realMatrix.val)) ⁻¹'
          Set.Iic (bound : ℝ) := by
    ext realMatrix
    simp only [integralBoundSet, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Iic]
  rw [equality]
  exact isClosed_iInter (fun finiteMatrix =>
    (matrixCuspSupNorm_lowerSemicontinuous inducedSection finiteMatrix).isClosed_preimage (bound : ℝ))

theorem integralBoundSet_cover {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction) :
    ⋃ bound : ℕ, integralBoundSet inducedSection bound = Set.univ := by
  apply Set.eq_univ_of_forall
  intro realMatrix
  obtain ⟨constant, _, boundProperty⟩ := integral_pointwise_bound inducedSection realMatrix
  obtain ⟨bound, boundConstant⟩ := exists_nat_ge constant
  exact Set.mem_iUnion.mpr ⟨bound, fun finiteMatrix => (boundProperty finiteMatrix).trans boundConstant⟩

/-- These bounds hold on a dense open set; membership of all orthogonal matrices is not asserted. -/
theorem integral_localBounds_dense {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction) :
    Dense (⋃ bound : ℕ, interior (integralBoundSet inducedSection bound)) := by
  have : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → ℝ))
  have : LocallyCompactSpace RealGL3 := inferInstance
  exact dense_iUnion_interior_of_closed (integralBoundSet_isClosed inducedSection)
    (integralBoundSet_cover inducedSection)

theorem integral_localBounds_isOpen {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction) :
    IsOpen (⋃ bound : ℕ, interior (integralBoundSet inducedSection bound)) :=
  isOpen_iUnion (fun _ => isOpen_interior)

theorem integralBoundSet_monotone {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction) :
    Monotone (integralBoundSet inducedSection) := by
  intro first second inequality realMatrix membership finiteMatrix
  exact (membership finiteMatrix).trans (by exact_mod_cast inequality)

theorem compact_bound_inside_localBounds {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    {compactSet : Set RealGL3} (compactness : IsCompact compactSet)
    (localBounds : compactSet ⊆ ⋃ bound : ℕ, interior (integralBoundSet inducedSection bound)) :
    ∃ bound : ℕ, ∀ realMatrix ∈ compactSet, ∀ finiteMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL,
      cuspSupNorm (matrixCuspVector inducedSection finiteMatrix realMatrix.val) ≤ bound := by
  have monotonicity : Monotone (fun bound : ℕ => interior (integralBoundSet inducedSection bound)) :=
    fun _ _ inequality => interior_mono (integralBoundSet_monotone inducedSection inequality)
  obtain ⟨bound, boundProperty⟩ := compactness.elim_directed_cover
    (fun bound : ℕ => interior (integralBoundSet inducedSection bound))
    (fun _ => isOpen_interior) localBounds monotonicity.directed_le
  exact ⟨bound, fun realMatrix membership => interior_subset (boundProperty membership)⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarLocalBounds
