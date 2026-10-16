module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Smooth.ParameterDerivative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CohomologicalLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CocycleDifferential

abbrev HilbertVectors (data : CuspidalRepresentation) (degree : ℕ) := Index (degree + 1) → data.H

noncomputable def hilbertAction (data : CuspidalRepresentation) (degree : ℕ) (matrix : BinaryRealGL) :
    HilbertVectors data degree →L[ℂ] HilbertVectors data degree :=
  ContinuousLinearMap.pi (fun index =>
    normPower (Matrix.GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2) •
      ∑ other : Index (degree + 1), (binaryCoefficient degree matrix (basisMonomial other)).val.coeff index.val •
        ((unitaryOperator data (atInfinity matrix)).comp (ContinuousLinearMap.proj other)))

theorem hilbertAction_apply (data : CuspidalRepresentation) (degree : ℕ) (matrix : BinaryRealGL)
    (vectors : HilbertVectors data degree) (index : Index (degree + 1)) :
    hilbertAction data degree matrix vectors index =
      normPower (Matrix.GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2) •
        ∑ other : Index (degree + 1), (binaryCoefficient degree matrix (basisMonomial other)).val.coeff index.val •
          data.π (atInfinity matrix) (vectors other) := by
  simp only [hilbertAction, ContinuousLinearMap.pi_apply, smul_apply,
    sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rfl

theorem hilbertAction_coefficientAction (data : CuspidalRepresentation) (degree : ℕ) (matrix : BinaryRealGL)
    (vectors : Vectors data degree) :
    hilbertAction data degree matrix (fun index => (vectors index).val) =
      (fun index => (coefficientAction data degree matrix vectors index).val) := by
  funext index
  rw [hilbertAction_apply]
  change _ = (normPower (Matrix.GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2) •
    ∑ other : Index (degree + 1), (binaryCoefficient degree matrix (basisMonomial other)).val.coeff index.val •
      smoothTranslate data matrix (vectors other)).val
  simp only [Submodule.coe_smul, Submodule.coe_sum]
  rfl

noncomputable def matrixCocycle (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree) (matrix : BinaryMatrix) : HilbertVectors data degree :=
  fun index => (cocycle (invertibleMatrix matrix) index).val

theorem matrixCocycle_contDiffOn (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (regularity : ∀ index : Index (degree + 1), Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (cocycle (x 0) index)).val)) :
    ContDiffOn ℝ ⊤ (matrixCocycle data degree cocycle) binaryDomain := by
  apply contDiffOn_pi.mpr
  intro index
  exact SmoothParameterDerivative.matrixFamily_contDiffOn data (fun matrix => cocycle matrix index) (regularity index)

theorem matrixCocycle_contDiffAt (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (regularity : ∀ index : Index (degree + 1), Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (cocycle (x 0) index)).val)) (matrix : BinaryRealGL) :
    ContDiffAt ℝ ⊤ (matrixCocycle data degree cocycle) matrix.val := by
  have membership : matrix.val ∈ binaryDomain := Matrix.GeneralLinearGroup.det_ne_zero matrix
  exact ((matrixCocycle_contDiffOn data degree cocycle regularity) matrix.val membership).contDiffAt
    (binaryDomain_isOpen.mem_nhds membership)

noncomputable def hilbertDifferential (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree) : BinaryMatrix →L[ℝ] HilbertVectors data degree :=
  fderiv ℝ (matrixCocycle data degree cocycle) 1

theorem hilbertDifferential_apply (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (regularity : ∀ index : Index (degree + 1), Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (cocycle (x 0) index)).val))
    (direction : BinaryMatrix) (index : Index (degree + 1)) :
    hilbertDifferential data degree cocycle direction index =
      SmoothParameterDerivative.derivative data (fun matrix => cocycle matrix index) direction := by
  have differentiability (position : Index (degree + 1)) :
      DifferentiableAt ℝ (SmoothParameterDerivative.matrixFamily data (fun matrix => cocycle matrix position)) 1 :=
    (SmoothParameterDerivative.matrixFamily_contDiffAt_one data _ (regularity position)).differentiableAt (by simp)
  have equality := fderiv_pi differentiability
  exact congrArg (fun linear : BinaryMatrix →L[ℝ] HilbertVectors data degree => linear direction index) equality

noncomputable def differential (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (regularity : ∀ index : Index (degree + 1), Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (cocycle (x 0) index)).val))
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactness : IsCompact (level : Set BinaryFiniteGL))
    (fixed : ∀ matrix index, (cocycle matrix index).val ∈ fixedSubspace data level) :
    BinaryMatrix →ₗ[ℝ] Vectors data degree :=
  LinearMap.pi (fun index => SmoothParameterDerivative.smoothDerivative data
    (fun matrix => cocycle matrix index) (regularity index) level openness compactness (fun matrix => fixed matrix index))

theorem differential_val (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (regularity : ∀ index : Index (degree + 1), Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (cocycle (x 0) index)).val))
    (level : Subgroup BinaryFiniteGL) (openness : IsOpen (level : Set BinaryFiniteGL))
    (compactness : IsCompact (level : Set BinaryFiniteGL))
    (fixed : ∀ matrix index, (cocycle matrix index).val ∈ fixedSubspace data level)
    (direction : BinaryMatrix) :
    (fun index => (differential data degree cocycle regularity level openness compactness fixed direction index).val) =
      hilbertDifferential data degree cocycle direction := by
  funext index
  exact (hilbertDifferential_apply data degree cocycle regularity direction index).symm

theorem cocycle_one (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (equation : ∀ first second, cocycle (first * second) =
      cocycle first + coefficientAction data degree first (cocycle second)) : cocycle 1 = 0 := by
  have equality := equation 1 1
  rw [one_mul, coefficientAction_one, Module.End.one_apply] at equality
  have difference := congrArg (fun value => value - cocycle 1) equality
  simpa only [sub_self, add_sub_cancel_right] using difference.symm

/-- The derivative of the actual lifted cocycle at any group point is the translated identity derivative. -/
theorem fderiv_cocycle_translate (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (regularity : ∀ index : Index (degree + 1), Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (cocycle (x 0) index)).val))
    (equation : ∀ first second, cocycle (first * second) =
      cocycle first + coefficientAction data degree first (cocycle second))
    (matrix : BinaryRealGL) (direction : BinaryMatrix) :
    fderiv ℝ (matrixCocycle data degree cocycle) matrix.val (matrix.val * direction) =
      hilbertAction data degree matrix (hilbertDifferential data degree cocycle direction) := by
  let action := (hilbertAction data degree matrix).restrictScalars ℝ
  have regularityAtOne : DifferentiableAt ℝ (matrixCocycle data degree cocycle) 1 :=
    (matrixCocycle_contDiffAt data degree cocycle regularity 1).differentiableAt (by simp)
  have regularityAtMatrix : DifferentiableAt ℝ (matrixCocycle data degree cocycle) matrix.val :=
    (matrixCocycle_contDiffAt data degree cocycle regularity matrix).differentiableAt (by simp)
  have atProduct : HasFDerivAt (matrixCocycle data degree cocycle)
      (fderiv ℝ (matrixCocycle data degree cocycle) matrix.val) ((leftMultiplication matrix.val) 1) := by
    rw [leftMultiplication_apply, mul_one]
    exact regularityAtMatrix.hasFDerivAt
  have productDerivative := atProduct.comp 1 (leftMultiplication matrix.val).hasFDerivAt
  have affineDerivative := (action.hasFDerivAt.comp 1 regularityAtOne.hasFDerivAt).const_add
    (fun index => (cocycle matrix index).val)
  have germ : matrixCocycle data degree cocycle ∘ leftMultiplication matrix.val =ᶠ[nhds (1 : BinaryMatrix)]
      (fun parameter => (fun index => (cocycle matrix index).val) + action (matrixCocycle data degree cocycle parameter)) := by
    filter_upwards [binaryDomain_isOpen.mem_nhds (show (1 : BinaryMatrix) ∈ binaryDomain by simp [binaryDomain])]
      with parameter invertibility
    change (fun index => (cocycle (invertibleMatrix (matrix.val * parameter)) index).val) = _
    rw [invertibleMatrix_left_mul matrix parameter invertibility, equation]
    change (fun index => (cocycle matrix index).val +
      (coefficientAction data degree matrix (cocycle (invertibleMatrix parameter)) index).val) =
      (fun index => (cocycle matrix index).val) +
        hilbertAction data degree matrix (fun index => (cocycle (invertibleMatrix parameter) index).val)
    rw [hilbertAction_coefficientAction]
    rfl
  have equality := productDerivative.unique (affineDerivative.congr_of_eventuallyEq germ)
  exact congrArg (fun linear : BinaryMatrix →L[ℝ] HilbertVectors data degree => linear direction) equality

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CocycleDifferential
