module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CasimirConjugation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieCasimir TernaryPeriodPolynomials.PlaneEisensteinContinuation.CasimirNorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.CasimirConjugation
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CasimirIrreducibility

noncomputable def smoothAction (data : CuspidalRepresentation) (matrix : BinaryAdelicGL) :
    Module.End ℂ data.smooth where
  toFun vector := ⟨data.π matrix vector.val, data.smooth_stable matrix vector.val vector.property⟩
  map_add' first second := Subtype.ext (map_add _ first.val second.val)
  map_smul' scalar vector := Subtype.ext (map_smul _ scalar vector.val)

theorem smoothAction_mul (data : CuspidalRepresentation) (first second : BinaryAdelicGL)
    (vector : data.smooth) :
    smoothAction data (first * second) vector = smoothAction data first (smoothAction data second vector) := by
  apply Subtype.ext
  exact congrArg (fun operator : Module.End ℂ data.H => operator vector.val) (map_mul data.π first second)

theorem directionalOperator_finite (data : CuspidalRepresentation) (matrix : BinaryFiniteGL)
    (vector : data.smooth) (direction : BinaryMatrix) :
    directionalOperator data direction (smoothAction data (atFinite matrix) vector) =
      smoothAction data (atFinite matrix) (directionalOperator data direction vector) := by
  let action := (unitaryOperator data (atFinite matrix)).restrictScalars ℝ
  have equality : action ∘ realOrbit data vector.val = realOrbit data (smoothAction data (atFinite matrix) vector).val := by
    funext value
    change data.π (atFinite matrix) (data.π (atInfinity (invertibleMatrix value)) vector.val) =
      data.π (atInfinity (invertibleMatrix value)) (data.π (atFinite matrix) vector.val)
    simp only [← Module.End.mul_apply, ← map_mul, TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute]
  have differentiability : DifferentiableAt ℝ (realOrbit data vector.val) 1 :=
    (smooth_orbit_contDiffAt_one data vector).differentiableAt (by simp)
  have derivative := action.hasFDerivAt.comp 1 differentiability.hasFDerivAt
  rw [equality] at derivative
  apply Subtype.ext
  exact congrArg (fun linear : BinaryMatrix →L[ℝ] data.H => linear direction) derivative.fderiv

theorem directional_square_finite (data : CuspidalRepresentation) (matrix : BinaryFiniteGL)
    (vector : data.smooth) (direction : BinaryMatrix) :
    (directionalOperator data direction ^ 2) (smoothAction data (atFinite matrix) vector) =
      smoothAction data (atFinite matrix) ((directionalOperator data direction ^ 2) vector) := by
  simp only [pow_two, Module.End.mul_apply, directionalOperator_finite]

theorem casimir_finite (data : CuspidalRepresentation) (matrix : BinaryFiniteGL) (vector : data.smooth) :
    casimir data (smoothAction data (atFinite matrix) vector) =
      smoothAction data (atFinite matrix) (casimir data vector) := by
  change (diagonalOperator data ^ 2) (smoothAction data (atFinite matrix) vector) +
      (symmetricOperator data ^ 2) (smoothAction data (atFinite matrix) vector) -
      (rotationOperator data ^ 2) (smoothAction data (atFinite matrix) vector) =
    smoothAction data (atFinite matrix) ((diagonalOperator data ^ 2) vector +
      (symmetricOperator data ^ 2) vector - (rotationOperator data ^ 2) vector)
  have diagonal : (diagonalOperator data ^ 2) (smoothAction data (atFinite matrix) vector) =
      smoothAction data (atFinite matrix) ((diagonalOperator data ^ 2) vector) :=
    directional_square_finite data matrix vector diagonalMatrix
  have symmetric : (symmetricOperator data ^ 2) (smoothAction data (atFinite matrix) vector) =
      smoothAction data (atFinite matrix) ((symmetricOperator data ^ 2) vector) :=
    directional_square_finite data matrix vector symmetricMatrix
  have rotation : (rotationOperator data ^ 2) (smoothAction data (atFinite matrix) vector) =
      smoothAction data (atFinite matrix) ((rotationOperator data ^ 2) vector) :=
    directional_square_finite data matrix vector rotationMatrix
  rw [diagonal, symmetric, rotation, map_sub, map_add]

theorem binaryAdelic_decomposition (matrix : BinaryAdelicGL) :
    matrix = atInfinity (Matrix.GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles) matrix) *
      atFinite (Matrix.GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles) matrix) := by
  rw [← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.combineGL_eq_mul]
  apply Units.ext
  rfl

theorem casimir_action (data : CuspidalRepresentation) (matrix : BinaryAdelicGL) (vector : data.smooth) :
    casimir data (smoothAction data matrix vector) = smoothAction data matrix (casimir data vector) := by
  rw [binaryAdelic_decomposition matrix]
  simp only [smoothAction_mul]
  have realEquality (realMatrix : BinaryRealGL) (value : data.smooth) :
      casimir data (smoothAction data (atInfinity realMatrix) value) =
        smoothAction data (atInfinity realMatrix) (casimir data value) := casimir_translate data realMatrix value
  rw [realEquality, casimir_finite]

noncomputable def eigenSpace (data : CuspidalRepresentation) (value : ℂ) : Submodule ℂ data.H :=
  (LinearMap.ker (casimir data - value • LinearMap.id)).map data.smooth.subtype

theorem mem_eigenSpace (data : CuspidalRepresentation) (value : ℂ) (vector : data.H) :
    vector ∈ eigenSpace data value ↔ ∃ smoothVector : data.smooth,
      casimir data smoothVector = value • smoothVector ∧ smoothVector.val = vector := by
  constructor
  · rintro ⟨smoothVector, kernelMembership, equality⟩
    exact ⟨smoothVector, sub_eq_zero.mp kernelMembership, equality⟩
  · rintro ⟨smoothVector, eigen, equality⟩
    exact ⟨smoothVector, sub_eq_zero.mpr eigen, equality⟩

theorem eigenSpace_stable (data : CuspidalRepresentation) (value : ℂ) (matrix : BinaryAdelicGL) :
    Set.MapsTo (data.π matrix) (eigenSpace data value : Set data.H) (eigenSpace data value : Set data.H) := by
  intro vector membership
  obtain ⟨smoothVector, eigen, rfl⟩ := (mem_eigenSpace data value vector).mp membership
  apply (mem_eigenSpace data value _).mpr
  refine ⟨smoothAction data matrix smoothVector, ?_, rfl⟩
  rw [casimir_action, eigen, map_smul]

theorem eigenSpace_dense (data : CuspidalRepresentation) (value : ℂ)
    (vector : data.smooth) (nonzero : vector ≠ 0) (eigen : casimir data vector = value • vector) :
    Dense (eigenSpace data value : Set data.H) := by
  have closureStable (matrix : BinaryAdelicGL) :
      Set.MapsTo (data.π matrix) ((eigenSpace data value).topologicalClosure : Set data.H)
        ((eigenSpace data value).topologicalClosure : Set data.H) :=
    (eigenSpace_stable data value matrix).closure (unitaryOperator data matrix).continuous
  have fullClosure : (eigenSpace data value).topologicalClosure = ⊤ := by
    rcases data.irreducible (eigenSpace data value).topologicalClosure
      (eigenSpace data value).isClosed_topologicalClosure
      (fun matrix _ membership => closureStable matrix membership) with zeroClosure | fullClosure
    · have member : vector.val ∈ eigenSpace data value := (mem_eigenSpace data value vector.val).mpr ⟨vector, eigen, rfl⟩
      have zeroVector : vector.val = 0 := by
        have closedMember := (eigenSpace data value).le_topologicalClosure member
        rw [zeroClosure] at closedMember
        exact closedMember
      exact False.elim (nonzero (Subtype.ext zeroVector))
    · exact fullClosure
  apply dense_iff_closure_eq.mpr
  change ((eigenSpace data value).topologicalClosure : Set data.H) = Set.univ
  rw [fullClosure]
  rfl

/-- A single nonzero smooth Casimir eigenvector forces the same eigenvalue on every smooth vector. -/
theorem casimir_scalar_of_eigenvector (data : CuspidalRepresentation) (value : ℂ)
    (vector : data.smooth) (nonzero : vector ≠ 0) (eigen : casimir data vector = value • vector)
    (other : data.smooth) : casimir data other = value • other := by
  have density := eigenSpace_dense data value vector nonzero eigen
  have realValue := casimir_eigen_real data vector nonzero value eigen
  have conjugateValue : starRingEnd ℂ value = value := by
    apply Complex.ext
    · simp
    · simp [realValue]
  apply Subtype.ext
  apply density.eq_of_inner_left ℂ
  intro test membership
  obtain ⟨smoothTest, testEigen, rfl⟩ := (mem_eigenSpace data value test).mp membership
  change inner ℂ (casimir data other).val smoothTest.val = inner ℂ (value • other.val) smoothTest.val
  rw [← casimir_inner, testEigen]
  change inner ℂ other.val (value • smoothTest.val) = inner ℂ (value • other.val) smoothTest.val
  rw [inner_smul_left, inner_smul_right, conjugateValue]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CasimirIrreducibility
