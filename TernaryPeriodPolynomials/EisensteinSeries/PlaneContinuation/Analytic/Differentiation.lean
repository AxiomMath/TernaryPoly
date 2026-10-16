module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.StageTranslation
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation

noncomputable instance derivativeOperatorNorm (data : CuspidalRepresentation) :
    NormedAddCommGroup (BinaryMatrix →L[ℝ] data.H) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable instance derivativeOperatorNormedSpace (data : CuspidalRepresentation) :
    NormedSpace ℝ (BinaryMatrix →L[ℝ] data.H) := ContinuousLinearMap.toNormedSpace

noncomputable def directionalVector (data : CuspidalRepresentation) (vector : data.smooth)
    (direction : BinaryMatrix) : data.H :=
  fderiv ℝ (realOrbit data vector.val) 1 direction

theorem directionalVector_eq_orbitDerivative (data : CuspidalRepresentation) (vector : data.smooth)
    (direction : BinaryMatrix) :
    directionalVector data vector direction =
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth.orbitDerivative data 1 vector.val (fun _ => direction) :=
  (iteratedFDeriv_one_apply (𝕜 := ℝ) (f := realOrbit data vector.val) (x := 1) (fun _ => direction)).symm

theorem directionalVector_translate (data : CuspidalRepresentation) (vector : data.smooth)
    (direction : BinaryMatrix) (matrix : BinaryRealGL) :
    data.π (atInfinity matrix) (directionalVector data vector direction) =
      fderiv ℝ (realOrbit data vector.val) matrix.val (matrix.val * direction) := by
  have formula := realOrbit_derivative_formula data vector matrix 1
  have evaluated := congrArg
    (fun derivative : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => BinaryMatrix) data.H =>
      derivative (fun _ => matrix.val * direction)) formula
  have cancellation : matrix⁻¹.val * (matrix.val * direction) = direction := by
    calc
      _ = (matrix⁻¹.val * matrix.val) * direction := (mul_assoc _ _ _).symm
      _ = direction := by
        have inverseProduct : matrix⁻¹.val * matrix.val = 1 := matrix.inv_val
        rw [inverseProduct, one_mul]
  change (iteratedFDeriv ℝ 1 (realOrbit data vector.val) matrix.val) (fun _ => matrix.val * direction) =
    data.π (atInfinity matrix)
      ((iteratedFDeriv ℝ 1 (realOrbit data vector.val) 1) (fun _ => matrix⁻¹.val * (matrix.val * direction))) at evaluated
  rw [iteratedFDeriv_one_apply, cancellation, iteratedFDeriv_one_apply] at evaluated
  exact evaluated.symm

theorem directionalVector_analyticAt_one (data : CuspidalRepresentation) (vector : data.smooth)
    (direction : BinaryMatrix) : AnalyticAt ℝ (realOrbit data (directionalVector data vector direction)) 1 := by
  have orbitAnalytic : AnalyticAt ℝ (realOrbit data vector.val) 1 :=
    (smooth_orbit_contDiffAt_one data vector).analyticAt
  have derivativeSmooth : ContDiffAt ℝ ⊤ (fderiv ℝ (realOrbit data vector.val)) 1 :=
    orbitAnalytic.fderiv.contDiffAt
  let rightMultiplication : BinaryMatrix →L[ℝ] BinaryMatrix :=
    ⟨LinearMap.mulRight ℝ direction, (LinearMap.mulRight ℝ direction).continuous_of_finiteDimensional⟩
  have modelSmooth : ContDiffAt ℝ ⊤
      (fun matrix : BinaryMatrix => fderiv ℝ (realOrbit data vector.val) matrix (matrix * direction)) 1 :=
    derivativeSmooth.clm_apply rightMultiplication.contDiff.contDiffAt
  have equality : realOrbit data (directionalVector data vector direction) =ᶠ[nhds (1 : BinaryMatrix)]
      (fun matrix => fderiv ℝ (realOrbit data vector.val) matrix (matrix * direction)) := by
    filter_upwards [binaryDomain_isOpen.mem_nhds (show (1 : BinaryMatrix) ∈ binaryDomain by simp [binaryDomain])]
      with matrix invertibility
    have formula := directionalVector_translate data vector direction (invertibleMatrix matrix)
    have matrixEquality : (invertibleMatrix matrix).val = matrix := invertibleMatrix_val matrix invertibility
    exact formula.trans (congrArg (fun point : BinaryMatrix =>
      fderiv ℝ (realOrbit data vector.val) point (point * direction)) matrixEquality)
  exact modelSmooth.analyticAt.congr equality.symm

theorem directionalVector_fixed (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (vector : data.smooth) (fixed : vector.val ∈ fixedSubspace data level) (direction : BinaryMatrix) :
    directionalVector data vector direction ∈ fixedSubspace data level := by
  intro element
  let action := (unitaryOperator data (atFinite element.val)).restrictScalars ℝ
  have functionEquality : action ∘ realOrbit data vector.val = realOrbit data vector.val := by
    funext matrix
    have commutation := congrArg (fun groupElement : BinaryAdelicGL => data.π groupElement vector.val)
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute element.val (invertibleMatrix matrix))
    simp only [map_mul, Module.End.mul_apply] at commutation
    change data.π (atFinite element.val) (data.π (atInfinity (invertibleMatrix matrix)) vector.val) =
      data.π (atInfinity (invertibleMatrix matrix)) vector.val
    rw [commutation, fixed element]
  have differentiability : DifferentiableAt ℝ (realOrbit data vector.val) 1 :=
    (smooth_orbit_contDiffAt_one data vector).differentiableAt (by simp)
  have derivative := action.hasFDerivAt.comp 1 differentiability.hasFDerivAt
  rw [functionEquality] at derivative
  exact (congrArg (fun linear : BinaryMatrix →L[ℝ] data.H => linear direction) derivative.fderiv).symm

theorem directionalVector_mem_smooth (data : CuspidalRepresentation) (vector : data.smooth)
    (direction : BinaryMatrix) : directionalVector data vector direction ∈ data.smooth := by
  obtain ⟨level, openness, compactness, fixed⟩ := ((data.smooth_exact vector.val).mp vector.property).2
  exact (TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticOrbit.fixed_mem_smooth_iff_analyticAt_one data level openness compactness
    (directionalVector data vector direction) (directionalVector_fixed data level vector fixed direction)).mpr
    (directionalVector_analyticAt_one data vector direction)

noncomputable def directionalOperator (data : CuspidalRepresentation) (direction : BinaryMatrix) :
    data.smooth →ₗ[ℂ] data.smooth where
  toFun vector := ⟨directionalVector data vector direction, directionalVector_mem_smooth data vector direction⟩
  map_add' first second := by
    apply Subtype.ext
    change directionalVector data (first + second) direction =
      directionalVector data first direction + directionalVector data second direction
    rw [directionalVector_eq_orbitDerivative, directionalVector_eq_orbitDerivative,
      directionalVector_eq_orbitDerivative, orbitDerivative_add, add_apply]
  map_smul' scalar vector := by
    apply Subtype.ext
    change directionalVector data (scalar • vector) direction = scalar • directionalVector data vector direction
    rw [directionalVector_eq_orbitDerivative, directionalVector_eq_orbitDerivative, orbitDerivative_smul, smul_apply]

theorem directionalOperator_preserves_fixed (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (direction : BinaryMatrix) (vector : data.smooth) (fixed : vector.val ∈ fixedSubspace data level) :
    (directionalOperator data direction vector).val ∈ fixedSubspace data level :=
  directionalVector_fixed data level vector fixed direction

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation
