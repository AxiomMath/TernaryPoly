module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.Level
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothBounds

noncomputable instance derivativeNormedAddCommGroup {size count order : ℕ} {Target : Type}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target] :
    NormedAddCommGroup (ContinuousMultilinearMap ℝ
      (fun _ : Fin order => Fin count → Matrix (Fin size) (Fin size) ℝ) Target) :=
  ContinuousMultilinearMap.normedAddCommGroup

def matrixDomain (size count : ℕ) : Set (Fin count → Matrix (Fin size) (Fin size) ℝ) :=
  {matrices | ∀ index, (matrices index).det ≠ 0}

theorem matrixDomain_isOpen (size count : ℕ) : IsOpen (matrixDomain size count) := by
  simp only [matrixDomain, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro index
  exact isOpen_ne.preimage (continuous_apply index).matrix_det

noncomputable def matrixLift {size count : ℕ} {Target : Type}
    (function : (Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ) → Target)
    (matrices : Fin count → Matrix (Fin size) (Fin size) ℝ) : Target :=
  function (fun index => invertibleMatrix (matrices index))

theorem matrixLift_at_units {size count : ℕ} {Target : Type}
    (function : (Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ) → Target)
    (matrices : Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ) :
    matrixLift function (fun index => (matrices index).val) = function matrices := by
  have equality : (fun index => invertibleMatrix (matrices index).val) = matrices := by
    funext index
    apply Units.ext
    simp [invertibleMatrix, Matrix.GeneralLinearGroup.det_ne_zero]
  exact congrArg function equality

noncomputable def matrixDerivative {size count : ℕ} {Target : Type}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (order : ℕ)
    (function : (Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ) → Target)
    (matrices : Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin order => Fin count → Matrix (Fin size) (Fin size) ℝ) Target :=
  iteratedFDerivWithin ℝ order (matrixLift function) (matrixDomain size count)
    (fun index => (matrices index).val)

theorem matrixDerivative_continuous {size count : ℕ} {Target : Type}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    {function : (Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ) → Target}
    (smoothFunction : Smooth function) (order : ℕ) :
    Continuous (matrixDerivative order function) := by
  have derivativeContinuous := smoothFunction.continuousOn_iteratedFDerivWithin
    (m := order) le_top (matrixDomain_isOpen size count).uniqueDiffOn
  exact derivativeContinuous.comp_continuous
    (continuous_pi (fun index => Units.continuous_val.comp (continuous_apply index)))
    (fun matrices index => Matrix.GeneralLinearGroup.det_ne_zero (matrices index))

theorem norm_matrixDerivative_zero {size count : ℕ} {Target : Type}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (function : (Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ) → Target)
    (matrices : Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ) :
    ‖matrixDerivative 0 function matrices‖ = ‖function matrices‖ := by
  exact (norm_iteratedFDerivWithin_zero (𝕜 := ℝ) (f := matrixLift function)
    (s := matrixDomain size count) (x := fun index => (matrices index).val)).trans
      (congrArg norm (matrixLift_at_units function matrices))

theorem matrixDerivative_bound {size count : ℕ} {Target : Type}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    {function : (Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ) → Target}
    (smoothFunction : Smooth function) (order : ℕ)
    {compactSet : Set (Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ)}
    (compactness : IsCompact compactSet) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ matrices ∈ compactSet,
      ‖matrixDerivative order function matrices‖ ≤ bound := by
  obtain ⟨bound, boundProperty⟩ := compactness.exists_bound_of_continuousOn
    (matrixDerivative_continuous smoothFunction order).continuousOn
  exact ⟨max 0 bound, le_max_left _ _, fun matrices membership =>
    (boundProperty matrices membership).trans (le_max_right _ _)⟩

theorem matrixDerivative_fixed {size count : ℕ} {Target : Type}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    {function : (Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ) → Target}
    (smoothFunction : Smooth function) (operator : Target →L[ℝ] Target)
    (fixed : ∀ matrices, operator (function matrices) = function matrices)
    (order : ℕ) (matrices : Fin count → Matrix.GeneralLinearGroup (Fin size) ℝ)
    (directions : Fin order → Fin count → Matrix (Fin size) (Fin size) ℝ) :
    operator (matrixDerivative order function matrices directions) =
      matrixDerivative order function matrices directions := by
  change ContDiffOn ℝ ⊤ (matrixLift function) (matrixDomain size count) at smoothFunction
  have membership : (fun index => (matrices index).val) ∈ matrixDomain size count :=
    fun index => Matrix.GeneralLinearGroup.det_ne_zero (matrices index)
  have composition : operator ∘ matrixLift function = matrixLift function := by
    funext values
    exact fixed _
  have formula := operator.iteratedFDerivWithin_comp_left (smoothFunction _ membership)
    (matrixDomain_isOpen size count).uniqueDiffOn membership (i := order) le_top
  rw [composition] at formula
  exact (congrArg (fun derivative => derivative directions) formula).symm

noncomputable def cuspDerivative {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (basePoint : AdelicGL) (order : ℕ) (realMatrix : RealGL3) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin order => Fin 1 → Matrix (Fin 3) (Fin 3) ℝ) data.cusp.H :=
  matrixDerivative order
    (fun matrices : Fin 1 → RealGL3 =>
      (planeCuspVector inducedSection (basePoint * atInfinity (matrices 0))).val)
    (fun _ => realMatrix)

theorem cuspDerivative_continuous {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (basePoint : AdelicGL) (order : ℕ) :
    Continuous (cuspDerivative inducedSection basePoint order) :=
  (matrixDerivative_continuous (planeCuspVector_smooth inducedSection basePoint) order).comp
    (continuous_pi (fun _ => continuous_id))

theorem cuspDerivative_bound_on_compact {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (basePoint : AdelicGL) (order : ℕ)
    {compactSet : Set RealGL3} (compactness : IsCompact compactSet) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ realMatrix ∈ compactSet,
      ‖cuspDerivative inducedSection basePoint order realMatrix‖ ≤ bound := by
  obtain ⟨bound, boundProperty⟩ := compactness.exists_bound_of_continuousOn
    (cuspDerivative_continuous inducedSection basePoint order).continuousOn
  exact ⟨max 0 bound, le_max_left _ _, fun realMatrix membership =>
    (boundProperty realMatrix membership).trans (le_max_right _ _)⟩

theorem cuspDerivative_same_integralReduction {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (first second : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL)
    (sameReduction : Matrix.GeneralLinearGroup.map integralReduction first =
      Matrix.GeneralLinearGroup.map integralReduction second)
    (order : ℕ) (realMatrix : RealGL3) :
    cuspDerivative inducedSection (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding first))
        order realMatrix =
      cuspDerivative inducedSection (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding second))
        order realMatrix := by
  have functionEquality :
      (fun matrices : Fin 1 → RealGL3 =>
        (planeCuspVector inducedSection
          (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding first) *
            atInfinity (matrices 0))).val) =
      (fun matrices : Fin 1 → RealGL3 =>
        (planeCuspVector inducedSection
          (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding second) *
            atInfinity (matrices 0))).val) := by
    funext matrices
    simp only [TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute]
    exact congrArg Subtype.val
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.planeCuspVector_same_integralReduction inducedSection
        (atInfinity (matrices 0)) first second sameReduction)
  exact congrArg (fun function => matrixDerivative order function (fun _ => realMatrix)) functionEquality

theorem cuspDerivative_integral_compact_bound {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction) (order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ realMatrix : RealGL3,
      realMatrix.val.transpose * realMatrix.val = 1 →
      ∀ integralMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL,
      ‖cuspDerivative inducedSection
        (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding integralMatrix))
        order realMatrix‖ ≤ bound := by
  classical
  let residues := Set.range (Matrix.GeneralLinearGroup.map integralReduction (n := Fin 3))
  let : Fintype residues := Fintype.ofFinite residues
  have pointwiseBounds (residue : residues) := cuspDerivative_bound_on_compact inducedSection
    (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.integralResidueRepresentative residue))) order
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Compact.isCompact_orthogonal
  choose bounds nonnegativeBounds boundProperty using pointwiseBounds
  refine ⟨∑ residue, bounds residue,
    Finset.sum_nonneg (fun residue _ => nonnegativeBounds residue),
    fun realMatrix orthogonality integralMatrix => ?_⟩
  let residue : residues :=
    ⟨Matrix.GeneralLinearGroup.map integralReduction integralMatrix, integralMatrix, rfl⟩
  rw [← cuspDerivative_same_integralReduction inducedSection
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.integralResidueRepresentative residue) integralMatrix
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.integralResidueRepresentative_reduction residue)]
  exact (boundProperty residue realMatrix orthogonality).trans
    (Finset.single_le_sum (fun residue _ => nonnegativeBounds residue) (Finset.mem_univ residue))

theorem cuspDerivative_maximalCompact_bound {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction) (order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ compactElement : AdelicGL,
      inMaximalCompact compactElement →
      ‖cuspDerivative inducedSection (atFinite (finiteGroup compactElement))
        order (realGroup compactElement)‖ ≤ bound := by
  obtain ⟨bound, nonnegativeBound, integralBound⟩ :=
    cuspDerivative_integral_compact_bound inducedSection order
  refine ⟨bound, nonnegativeBound, fun compactElement compactness => ?_⟩
  obtain ⟨integralMatrix, finiteEquality⟩ := compactness.2
  rw [← finiteEquality]
  exact integralBound (realGroup compactElement) compactness.1 integralMatrix

noncomputable def compactDerivativeSum {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (order : ℕ) (matrix : AdelicGL) : ℝ :=
  ∑ index ∈ Finset.range (order + 1),
    ‖cuspDerivative inducedSection (atFinite (finiteGroup matrix)) index (realGroup matrix)‖

theorem compactDerivativeSum_nonneg {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (order : ℕ) (matrix : AdelicGL) : 0 ≤ compactDerivativeSum inducedSection order matrix :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem norm_cuspVector_le_compactDerivativeSum {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction)
    (order : ℕ) (matrix : AdelicGL) :
    ‖(planeCuspVector inducedSection matrix).val‖ ≤ compactDerivativeSum inducedSection order matrix := by
  have zeroDerivative :
      ‖cuspDerivative inducedSection (atFinite (finiteGroup matrix)) 0 (realGroup matrix)‖ =
        ‖(planeCuspVector inducedSection matrix).val‖ := by
    rw [cuspDerivative, norm_matrixDerivative_zero]
    dsimp only
    rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute, ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adelicGL_eq_mul]
  rw [← zeroDerivative]
  exact Finset.single_le_sum (fun index _ => norm_nonneg
    (cuspDerivative inducedSection (atFinite (finiteGroup matrix)) index (realGroup matrix)))
    (Finset.mem_range.mpr (Nat.zero_lt_succ order))

theorem compactDerivativeSum_bound {degree : ℕ} {data : InducingData degree}
    {parameter : ℂ} {sectionFunction : AdelicGL → ℂ}
    (inducedSection : IsInduced data .plane parameter sectionFunction) (order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ compactElement : AdelicGL,
      inMaximalCompact compactElement → compactDerivativeSum inducedSection order compactElement ≤ bound := by
  choose bounds nonnegativeBounds boundProperty using cuspDerivative_maximalCompact_bound inducedSection
  refine ⟨∑ index ∈ Finset.range (order + 1), bounds index,
    Finset.sum_nonneg (fun index _ => nonnegativeBounds index), fun compactElement compactness => ?_⟩
  exact Finset.sum_le_sum (fun index _ => boundProperty index compactElement compactness)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothBounds
