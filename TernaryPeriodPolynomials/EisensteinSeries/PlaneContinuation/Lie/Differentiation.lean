module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.SupNormOrbit
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieDifferentiation

theorem directionalOperator_add (data : CuspidalRepresentation) (first second : BinaryMatrix) :
    directionalOperator data (first + second) = directionalOperator data first + directionalOperator data second := by
  apply LinearMap.ext
  intro vector
  exact map_add (directionalSmooth data vector) first second

theorem directionalOperator_sub (data : CuspidalRepresentation) (first second : BinaryMatrix) :
    directionalOperator data (first - second) = directionalOperator data first - directionalOperator data second := by
  apply LinearMap.ext
  intro vector
  exact map_sub (directionalSmooth data vector) first second

theorem directionalOperator_real_smul (data : CuspidalRepresentation) (scalar : ℝ) (direction : BinaryMatrix) :
    directionalOperator data (scalar • direction) = (scalar : ℂ) • directionalOperator data direction := by
  apply LinearMap.ext
  intro vector
  have equality := map_smul (directionalSmooth data vector) scalar direction
  exact equality

theorem directionalVector_comp (data : CuspidalRepresentation) (vector : data.smooth)
    (first second : BinaryMatrix) :
    directionalVector data (directionalOperator data second vector) first =
      fderiv ℝ (fderiv ℝ (realOrbit data vector.val)) 1 first second +
        directionalVector data vector (first * second) := by
  let rightMultiplication : BinaryMatrix →L[ℝ] BinaryMatrix :=
    ⟨LinearMap.mulRight ℝ second, (LinearMap.mulRight ℝ second).continuous_of_finiteDimensional⟩
  have regularity : ContDiffAt ℝ ⊤ (fderiv ℝ (realOrbit data vector.val)) 1 :=
    (smooth_orbit_contDiffAt_one data vector).analyticAt.fderiv.contDiffAt
  have derivative := (regularity.differentiableAt (by simp)).hasFDerivAt.clm_apply rightMultiplication.hasFDerivAt
  have germ : realOrbit data (directionalOperator data second vector).val =ᶠ[nhds (1 : BinaryMatrix)]
      (fun matrix => fderiv ℝ (realOrbit data vector.val) matrix (matrix * second)) := by
    filter_upwards [binaryDomain_isOpen.mem_nhds (show (1 : BinaryMatrix) ∈ binaryDomain by simp [binaryDomain])]
      with matrix invertibility
    have equality := directionalVector_translate data vector second (invertibleMatrix matrix)
    rw [invertibleMatrix_val matrix invertibility] at equality
    exact equality
  have equality := (derivative.congr_of_eventuallyEq germ).fderiv
  have evaluated := congrArg (fun linear : BinaryMatrix →L[ℝ] data.H => linear first) equality
  change directionalVector data (directionalOperator data second vector) first =
    fderiv ℝ (realOrbit data vector.val) 1 (first * second) +
      fderiv ℝ (fderiv ℝ (realOrbit data vector.val)) 1 first ((1 : BinaryMatrix) * second) at evaluated
  rw [one_mul, add_comm] at evaluated
  exact evaluated

/-- Differentiation of the actual unitary action respects the matrix commutator. -/
theorem directionalOperator_commutator (data : CuspidalRepresentation) (first second : BinaryMatrix) :
    directionalOperator data first * directionalOperator data second -
      directionalOperator data second * directionalOperator data first =
        directionalOperator data (first * second - second * first) := by
  apply LinearMap.ext
  intro vector
  apply Subtype.ext
  change directionalVector data (directionalOperator data second vector) first -
    directionalVector data (directionalOperator data first vector) second =
      directionalVector data vector (first * second - second * first)
  rw [directionalVector_comp, directionalVector_comp]
  have symmetry : fderiv ℝ (fderiv ℝ (realOrbit data vector.val)) 1 first second =
      fderiv ℝ (fderiv ℝ (realOrbit data vector.val)) 1 second first :=
    (smooth_orbit_contDiffAt_one data vector).isSymmSndFDerivAt_of_omega.eq first second
  rw [symmetry]
  change _ = fderiv ℝ (realOrbit data vector.val) 1 (first * second - second * first)
  rw [map_sub]
  abel

theorem realOrbit_inner (data : CuspidalRepresentation) (first second : data.H) (matrix : BinaryMatrix) :
    inner ℂ (realOrbit data first matrix) (realOrbit data second matrix) = inner ℂ first second := by
  let isometry : data.H →ₗᵢ[ℂ] data.H :=
    ⟨data.π (atInfinity (invertibleMatrix matrix)), data.unitary (atInfinity (invertibleMatrix matrix))⟩
  exact isometry.inner_map_map first second

/-- Every real infinitesimal direction is skew with respect to the supplied Hilbert inner product. -/
theorem directionalOperator_inner (data : CuspidalRepresentation) (first second : data.smooth)
    (direction : BinaryMatrix) :
    inner ℂ first.val (directionalOperator data direction second).val +
      inner ℂ (directionalOperator data direction first).val second.val = 0 := by
  have firstDerivative : HasFDerivAt (realOrbit data first.val)
      (fderiv ℝ (realOrbit data first.val) 1) 1 :=
    ((smooth_orbit_contDiffAt_one data first).differentiableAt (by simp)).hasFDerivAt
  have secondDerivative : HasFDerivAt (realOrbit data second.val)
      (fderiv ℝ (realOrbit data second.val) 1) 1 :=
    ((smooth_orbit_contDiffAt_one data second).differentiableAt (by simp)).hasFDerivAt
  have derivative := firstDerivative.inner ℂ secondDerivative
  have equality : (fun matrix : BinaryMatrix => inner ℂ (realOrbit data first.val matrix)
      (realOrbit data second.val matrix)) = (fun _ : BinaryMatrix => inner ℂ first.val second.val) :=
    funext (realOrbit_inner data first.val second.val)
  rw [equality] at derivative
  have derivativeEquality := derivative.unique (hasFDerivAt_const (inner ℂ first.val second.val) (1 : BinaryMatrix))
  have evaluated := congrArg (fun linear : BinaryMatrix →L[ℝ] ℂ => linear direction) derivativeEquality
  change inner ℂ (realOrbit data first.val 1) (directionalVector data second direction) +
    inner ℂ (directionalVector data first direction) (realOrbit data second.val 1) = 0 at evaluated
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticOrbit.realOrbit_one, TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticOrbit.realOrbit_one] at evaluated
  exact evaluated

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieDifferentiation
