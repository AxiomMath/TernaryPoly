module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ZeroCocycleDifferential

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CohomologicalLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CocycleDifferential
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieCocycle

noncomputable instance differentialNorm (data : CuspidalRepresentation) (degree : ℕ) :
    NormedAddCommGroup (BinaryMatrix →L[ℝ] HilbertVectors data degree) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable instance differentialNormedSpace (data : CuspidalRepresentation) (degree : ℕ) :
    NormedSpace ℝ (BinaryMatrix →L[ℝ] HilbertVectors data degree) := ContinuousLinearMap.toNormedSpace

noncomputable def infinitesimalAction (data : CuspidalRepresentation) (degree : ℕ)
    (direction : BinaryMatrix) (vectors : HilbertVectors data degree) : HilbertVectors data degree :=
  fderiv ℝ (fun matrix : BinaryMatrix => hilbertAction data degree (invertibleMatrix matrix) vectors) 1 direction

theorem infinitesimal_differential (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (regularity : ∀ index : Index (degree + 1), Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (cocycle (x 0) index)).val))
    (equation : ∀ first second, cocycle (first * second) =
      cocycle first + coefficientAction data degree first (cocycle second))
    (first second : BinaryMatrix) :
    infinitesimalAction data degree first (hilbertDifferential data degree cocycle second) =
      fderiv ℝ (fderiv ℝ (matrixCocycle data degree cocycle)) 1 first second +
        hilbertDifferential data degree cocycle (first * second) := by
  let rightMultiplication : BinaryMatrix →L[ℝ] BinaryMatrix :=
    ⟨LinearMap.mulRight ℝ second, (LinearMap.mulRight ℝ second).continuous_of_finiteDimensional⟩
  have regularityAtOne : ContDiffAt ℝ ⊤ (matrixCocycle data degree cocycle) 1 :=
    matrixCocycle_contDiffAt data degree cocycle regularity 1
  have derivativeRegularity : ContDiffAt ℝ ⊤ (fderiv ℝ (matrixCocycle data degree cocycle)) 1 :=
    regularityAtOne.analyticAt.fderiv.contDiffAt
  have derivative := (derivativeRegularity.differentiableAt (by simp)).hasFDerivAt.clm_apply rightMultiplication.hasFDerivAt
  have germ : (fun matrix : BinaryMatrix =>
      hilbertAction data degree (invertibleMatrix matrix) (hilbertDifferential data degree cocycle second)) =ᶠ[nhds (1 : BinaryMatrix)]
      (fun matrix => fderiv ℝ (matrixCocycle data degree cocycle) matrix (matrix * second)) := by
    filter_upwards [binaryDomain_isOpen.mem_nhds (show (1 : BinaryMatrix) ∈ binaryDomain by simp [binaryDomain])]
      with matrix invertibility
    have equality := fderiv_cocycle_translate data degree cocycle regularity equation (invertibleMatrix matrix) second
    rw [invertibleMatrix_val matrix invertibility] at equality
    exact equality.symm
  have equality := (derivative.congr_of_eventuallyEq germ).fderiv
  have evaluated := congrArg (fun linear : BinaryMatrix →L[ℝ] HilbertVectors data degree => linear first) equality
  change infinitesimalAction data degree first (hilbertDifferential data degree cocycle second) =
    hilbertDifferential data degree cocycle (first * second) +
      fderiv ℝ (fderiv ℝ (matrixCocycle data degree cocycle)) 1 first ((1 : BinaryMatrix) * second) at evaluated
  rw [one_mul] at evaluated
  exact evaluated.trans (add_comm _ _)

/-- Differentiating the actual lifted group cocycle gives the Lie cocycle identity. -/
theorem cocycle_identity (data : CuspidalRepresentation) (degree : ℕ)
    (cocycle : BinaryRealGL → Vectors data degree)
    (regularity : ∀ index : Index (degree + 1), Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (cocycle (x 0) index)).val))
    (equation : ∀ first second, cocycle (first * second) =
      cocycle first + coefficientAction data degree first (cocycle second))
    (first second : BinaryMatrix) :
    infinitesimalAction data degree first (hilbertDifferential data degree cocycle second) -
      infinitesimalAction data degree second (hilbertDifferential data degree cocycle first) =
        hilbertDifferential data degree cocycle (first * second - second * first) := by
  rw [infinitesimal_differential data degree cocycle regularity equation,
    infinitesimal_differential data degree cocycle regularity equation]
  have regularityAtOne : ContDiffAt ℝ ⊤ (matrixCocycle data degree cocycle) 1 :=
    matrixCocycle_contDiffAt data degree cocycle regularity 1
  have symmetry : fderiv ℝ (fderiv ℝ (matrixCocycle data degree cocycle)) 1 first second =
      fderiv ℝ (fderiv ℝ (matrixCocycle data degree cocycle)) 1 second first :=
    regularityAtOne.isSymmSndFDerivAt_of_omega.eq first second
  rw [symmetry, map_sub]
  abel

/-- The supplied nonzero group cohomology gives a nonzero smooth, finite-level Lie cocycle. -/
theorem exists_nonzero_differential {degree : ℕ} (data : InducingData degree) :
    ∃ differential : BinaryMatrix →L[ℝ] HilbertVectors data.cusp degree,
      differential ≠ 0 ∧
      (∀ direction index, differential direction index ∈ data.cusp.smooth) ∧
      (∃ level : Subgroup BinaryFiniteGL, IsOpen (level : Set BinaryFiniteGL) ∧
        IsCompact (level : Set BinaryFiniteGL) ∧ ∀ direction index,
          differential direction index ∈ fixedSubspace data.cusp level) ∧
      ∀ first second, infinitesimalAction data.cusp degree first (differential second) -
        infinitesimalAction data.cusp degree second (differential first) = differential (first * second - second * first) := by
  obtain ⟨cocycle, regularity, ⟨level, openness, compactness, fixed⟩, equation, nontrivialClass⟩ :=
    exists_lifted_cocycle data
  have fixedCoordinates (matrix : BinaryRealGL) (index : Index (degree + 1)) :
      (cocycle matrix index).val ∈ fixedSubspace data.cusp level := fun element => fixed element matrix index
  refine ⟨hilbertDifferential data.cusp degree cocycle,
    ZeroCocycleDifferential.differential_ne_zero data.cusp degree cocycle regularity equation nontrivialClass,
    ?_, ⟨level, openness, compactness, ?_⟩, cocycle_identity data.cusp degree cocycle regularity equation⟩
  · intro direction index
    rw [hilbertDifferential_apply data.cusp degree cocycle regularity]
    exact SmoothParameterDerivative.derivative_mem_smooth data.cusp (fun matrix => cocycle matrix index)
      (regularity index) level openness compactness (fun matrix => fixedCoordinates matrix index) direction
  · intro direction index
    rw [hilbertDifferential_apply data.cusp degree cocycle regularity]
    exact SmoothParameterDerivative.derivative_fixed data.cusp (fun matrix => cocycle matrix index)
      (regularity index) level (fun matrix => fixedCoordinates matrix index) direction

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieCocycle
