module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rotation.Primitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CohomologicalLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CocycleDifferential
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientInfinitesimal TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientSmoothAction TernaryPeriodPolynomials.PlaneEisensteinContinuation.DifferentiatedCohomology
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientLieAction

noncomputable def coboundary (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (matrix : BinaryRealGL) : Vectors data degree := coefficientAction data degree matrix vectors - vectors

theorem coboundary_smooth (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (index : Index (degree + 1)) : Smooth (fun x : Fin 2 → BinaryRealGL =>
      (smoothTranslate data (x 1) (coboundary data degree vectors (x 0) index)).val) := by
  have regularity := (coefficientAction_joint_smooth data degree vectors index).sub
    (constant_family_joint_smooth data (vectors index))
  change ContDiffOn ℝ ⊤ _ _
  convert regularity using 1
  funext matrices
  change (smoothTranslate data (invertibleMatrix (matrices 1))
    (coefficientAction data degree (invertibleMatrix (matrices 0)) vectors index - vectors index)).val = _
  simp only [map_sub, Submodule.coe_sub]

theorem coboundary_equation (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (first second : BinaryRealGL) : coboundary data degree vectors (first * second) =
      coboundary data degree vectors first + coefficientAction data degree first (coboundary data degree vectors second) := by
  simp only [coboundary, coefficientAction_mul, Module.End.mul_apply, map_sub]
  abel

theorem differential_coboundary (data : CuspidalRepresentation) (degree : ℕ) (vectors : Vectors data degree)
    (direction : BinaryMatrix) : hilbertDifferential data degree (coboundary data degree vectors) direction =
      LieCocycle.infinitesimalAction data degree direction (fun index => (vectors index).val) := by
  have derivative := (((coefficient_orbit_contDiffAt_one data degree vectors).differentiableAt (by simp)).hasFDerivAt).sub_const
    (fun index => (vectors index).val)
  have functionEquality : (fun matrix : BinaryMatrix =>
      hilbertAction data degree (invertibleMatrix matrix) (fun index => (vectors index).val) -
        (fun index => (vectors index).val)) = matrixCocycle data degree (coboundary data degree vectors) := by
    funext matrix
    rw [hilbertAction_coefficientAction]
    rfl
  rw [functionEquality] at derivative
  exact congrArg (fun linear : BinaryMatrix →L[ℝ] HilbertVectors data degree => linear direction) derivative.fderiv

/-- The differentiated coefficient operators form the actual Lie representation. -/
theorem operator_commutator (data : CuspidalRepresentation) (degree : ℕ) (first second : BinaryMatrix) :
    operator data degree first * operator data degree second - operator data degree second * operator data degree first =
      operator data degree (first * second - second * first) := by
  apply LinearMap.ext
  intro vectors
  have equation := LieCocycle.cocycle_identity data degree (coboundary data degree vectors)
    (coboundary_smooth data degree vectors) (coboundary_equation data degree vectors) first second
  simp only [differential_coboundary] at equation
  rw [← operator_val data degree second vectors, ← operator_val data degree first vectors,
    ← operator_val data degree first (operator data degree second vectors),
    ← operator_val data degree second (operator data degree first vectors),
    ← operator_val data degree (first * second - second * first) vectors] at equation
  funext index
  apply Subtype.ext
  exact congrFun equation index

noncomputable def infinitesimalCoboundary (data : CuspidalRepresentation) (degree : ℕ)
    (vectors : Vectors data degree) : BinaryMatrix →ₗ[ℝ] Vectors data degree where
  toFun direction := operator data degree direction vectors
  map_add' first second := congrArg (fun linear : Module.End ℂ (Vectors data degree) => linear vectors)
    (operator_add data degree first second)
  map_smul' scalar direction := congrArg (fun linear : Module.End ℂ (Vectors data degree) => linear vectors)
    (operator_real_smul data degree scalar direction)

theorem infinitesimalCoboundary_equation (data : CuspidalRepresentation) (degree : ℕ)
    (vectors : Vectors data degree) (first second : BinaryMatrix) :
    operator data degree first (infinitesimalCoboundary data degree vectors second) -
      operator data degree second (infinitesimalCoboundary data degree vectors first) =
        infinitesimalCoboundary data degree vectors (first * second - second * first) :=
  congrArg (fun linear : Module.End ℂ (Vectors data degree) => linear vectors) (operator_commutator data degree first second)

theorem residual_equation (data : CuspidalRepresentation) (degree : ℕ)
    (differential : BinaryMatrix →ₗ[ℝ] Vectors data degree)
    (equation : ∀ first second, operator data degree first (differential second) -
      operator data degree second (differential first) = differential (first * second - second * first))
    (vectors : Vectors data degree) (first second : BinaryMatrix) :
    operator data degree first ((differential - infinitesimalCoboundary data degree vectors) second) -
      operator data degree second ((differential - infinitesimalCoboundary data degree vectors) first) =
        (differential - infinitesimalCoboundary data degree vectors) (first * second - second * first) := by
  simp only [LinearMap.sub_apply, map_sub]
  have original := equation first second
  have exactEquation := infinitesimalCoboundary_equation data degree vectors first second
  calc
    _ = (operator data degree first (differential second) - operator data degree second (differential first)) -
        (operator data degree first (infinitesimalCoboundary data degree vectors second) -
          operator data degree second (infinitesimalCoboundary data degree vectors first)) := by abel
    _ = differential (first * second - second * first) -
        infinitesimalCoboundary data degree vectors (first * second - second * first) :=
      congrArg₂ (· - ·) original exactEquation
    _ = _ := by rw [map_sub, map_sub]; abel

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientLieAction
