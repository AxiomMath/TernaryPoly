module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.CoefficientRegularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CohomologicalLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CocycleDifferential
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryCoefficientRegularity
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientSmoothAction

theorem matrixProduct_contDiff : ContDiff ℝ ⊤ (fun matrices : Fin 2 → BinaryMatrix => matrices 1 * matrices 0) := by
  apply contDiff_pi.mpr
  intro row
  apply contDiff_pi.mpr
  intro column
  simp only [Matrix.mul_apply]
  apply ContDiff.sum
  intro middle _
  exact ((contDiff_apply_apply ℝ ℝ row middle).comp (contDiff_apply ℝ BinaryMatrix 1)).mul
    ((contDiff_apply_apply ℝ ℝ middle column).comp (contDiff_apply ℝ BinaryMatrix 0))

theorem joint_orbit_contDiffOn (data : CuspidalRepresentation) (vector : data.smooth) :
    ContDiffOn ℝ ⊤ (fun matrices : Fin 2 → BinaryMatrix => realOrbit data vector.val (matrices 1 * matrices 0))
      {matrices | ∀ position, (matrices position).det ≠ 0} := by
  apply (smooth_orbit_contDiffOn data vector).comp matrixProduct_contDiff.contDiffOn
  intro matrices membership
  change (matrices 1 * matrices 0).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero (membership 1) (membership 0)

theorem coefficientAction_joint_smooth (data : CuspidalRepresentation) (degree : ℕ)
    (vectors : Vectors data degree) (index : Index (degree + 1)) :
    Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (coefficientAction data degree (x 0) vectors index)).val) := by
  let multiplier := fun (matrices : Fin 2 → BinaryMatrix) (other : Index (degree + 1)) =>
    normPower (Matrix.GeneralLinearGroup.det (atInfinity (invertibleMatrix (matrices 0)))) (((degree : ℂ) + 3) / 2) *
      (binaryCoefficient degree (invertibleMatrix (matrices 0)) (basisMonomial other)).val.coeff index.val
  have multiplierRegular (other : Index (degree + 1)) :
      ContDiffOn ℝ ⊤ (fun matrices : Fin 2 → BinaryMatrix => multiplier matrices other)
        {matrices | ∀ position, (matrices position).det ≠ 0} := by
    intro matrices membership
    exact ((multiplier_contDiffAt degree index other (matrices 0) (membership 0)).comp matrices
      (contDiff_apply ℝ BinaryMatrix 0).contDiffAt).contDiffWithinAt
  have modelRegular : ContDiffOn ℝ ⊤ (fun matrices : Fin 2 → BinaryMatrix =>
      ∑ other : Index (degree + 1), multiplier matrices other • realOrbit data (vectors other).val (matrices 1 * matrices 0))
      {matrices | ∀ position, (matrices position).det ≠ 0} := by
    apply ContDiffOn.sum
    intro other _
    exact (multiplierRegular other).smul (joint_orbit_contDiffOn data (vectors other))
  apply modelRegular.congr
  intro matrices invertibility
  have productEquality : invertibleMatrix (matrices 1 * matrices 0) =
      invertibleMatrix (matrices 1) * invertibleMatrix (matrices 0) := by
    have equality := invertibleMatrix_left_mul (invertibleMatrix (matrices 1)) (matrices 0) (invertibility 0)
    rw [invertibleMatrix_val (matrices 1) (invertibility 1)] at equality
    exact equality
  change data.π (atInfinity (invertibleMatrix (matrices 1)))
    (normPower (Matrix.GeneralLinearGroup.det (atInfinity (invertibleMatrix (matrices 0)))) (((degree : ℂ) + 3) / 2) •
      ∑ other : Index (degree + 1),
        (binaryCoefficient degree (invertibleMatrix (matrices 0)) (basisMonomial other)).val.coeff index.val •
          smoothTranslate data (invertibleMatrix (matrices 0)) (vectors other)).val = _
  simp only [Submodule.coe_smul, Submodule.coe_sum, map_smul, map_sum, Finset.smul_sum, smul_smul,
    multiplier, realOrbit, productEquality, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul, map_mul, Module.End.mul_apply]
  rfl

theorem coefficient_orbit_contDiffOn (data : CuspidalRepresentation) (degree : ℕ)
    (vectors : Vectors data degree) :
    ContDiffOn ℝ ⊤
      (fun matrix : BinaryMatrix => hilbertAction data degree (invertibleMatrix matrix) (fun index => (vectors index).val))
      binaryDomain := by
  have regularity := matrixCocycle_contDiffOn data degree (fun matrix => coefficientAction data degree matrix vectors)
    (coefficientAction_joint_smooth data degree vectors)
  have equality : (fun matrix : BinaryMatrix =>
      hilbertAction data degree (invertibleMatrix matrix) (fun index => (vectors index).val)) =
      matrixCocycle data degree (fun matrix => coefficientAction data degree matrix vectors) := by
    funext matrix
    exact hilbertAction_coefficientAction data degree (invertibleMatrix matrix) vectors
  rw [equality]
  exact regularity

theorem coefficient_orbit_contDiffAt_one (data : CuspidalRepresentation) (degree : ℕ)
    (vectors : Vectors data degree) :
    ContDiffAt ℝ ⊤
      (fun matrix : BinaryMatrix => hilbertAction data degree (invertibleMatrix matrix) (fun index => (vectors index).val)) 1 := by
  have membership : (1 : BinaryMatrix) ∈ binaryDomain := by simp [binaryDomain]
  exact ((coefficient_orbit_contDiffOn data degree vectors) 1 membership).contDiffAt
    (binaryDomain_isOpen.mem_nhds membership)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientSmoothAction
