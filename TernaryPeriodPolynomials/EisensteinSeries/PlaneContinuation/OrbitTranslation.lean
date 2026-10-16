module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.SobolevSeminorms

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation

noncomputable instance multiplicationOperatorNorm : NormedAddCommGroup (BinaryMatrix →L[ℝ] BinaryMatrix) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable def leftMultiplication (matrix : BinaryMatrix) : BinaryMatrix →L[ℝ] BinaryMatrix :=
  ⟨LinearMap.mulLeft ℝ matrix, (LinearMap.mulLeft ℝ matrix).continuous_of_finiteDimensional⟩

theorem leftMultiplication_apply (matrix value : BinaryMatrix) :
    leftMultiplication matrix value = matrix * value := rfl

noncomputable def realOrbit (data : CuspidalRepresentation) (vector : data.H) (matrix : BinaryMatrix) :
    data.H := data.π (atInfinity (invertibleMatrix matrix)) vector

theorem invertibleMatrix_left_mul (matrix : BinaryRealGL) (value : BinaryMatrix)
    (invertibility : value.det ≠ 0) :
    invertibleMatrix (matrix.val * value) = matrix * invertibleMatrix value := by
  apply Units.ext
  have productInvertibility : (matrix.val * value).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero matrix) invertibility
  rw [invertibleMatrix_val _ productInvertibility, Matrix.GeneralLinearGroup.coe_mul,
    invertibleMatrix_val value invertibility]

theorem realOrbit_inverse_translation (data : CuspidalRepresentation) (vector : data.H)
    (matrix : BinaryRealGL) (value : BinaryMatrix) (invertibility : value.det ≠ 0) :
    data.π (atInfinity matrix) (realOrbit data vector (matrix⁻¹.val * value)) =
      realOrbit data vector value := by
  rw [realOrbit, invertibleMatrix_left_mul matrix⁻¹ value invertibility,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul, map_mul, Module.End.mul_apply,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth.atInfinity_inv, ← Module.End.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply]
  rfl

theorem realOrbit_derivative_formula (data : CuspidalRepresentation) (vector : data.smooth)
    (matrix : BinaryRealGL) (order : ℕ) :
    iteratedFDeriv ℝ order (realOrbit data vector.val) matrix.val =
      ((unitaryOperator data (atInfinity matrix)).restrictScalars ℝ).compContinuousMultilinearMap
        ((orbitDerivative data order vector.val).compContinuousLinearMap
          (fun _ => leftMultiplication matrix⁻¹.val)) := by
  let inverseTranslation := leftMultiplication matrix⁻¹.val
  let action := (unitaryOperator data (atInfinity matrix)).restrictScalars ℝ
  have inverseAtPoint : inverseTranslation matrix.val = (1 : BinaryMatrix) := matrix.inv_val
  have smoothAtIdentity : ContDiffAt ℝ ⊤ (realOrbit data vector.val) 1 :=
    smooth_orbit_contDiffAt_one data vector
  have smoothAtTranslated : ContDiffAt ℝ ⊤ (realOrbit data vector.val) (inverseTranslation matrix.val) :=
    (congrArg (fun point : BinaryMatrix => ContDiffAt ℝ ⊤ (realOrbit data vector.val) point)
      inverseAtPoint).mpr smoothAtIdentity
  have composition := iteratedFDeriv_comp_linear_at inverseTranslation (realOrbit data vector.val)
    matrix.val smoothAtTranslated order
  have atIdentity := congrArg (fun point : BinaryMatrix =>
    (iteratedFDeriv ℝ order (realOrbit data vector.val) point).compContinuousLinearMap
      (fun _ => inverseTranslation)) inverseAtPoint
  have smoothComposite : ContDiffAt ℝ ⊤ ((realOrbit data vector.val) ∘ inverseTranslation) matrix.val :=
    smoothAtTranslated.comp matrix.val inverseTranslation.contDiff.contDiffAt
  have actionComposition := action.iteratedFDeriv_comp_left smoothComposite (i := order) le_top
  have germEquality : realOrbit data vector.val =ᶠ[nhds matrix.val]
      action ∘ (realOrbit data vector.val) ∘ inverseTranslation := by
    filter_upwards [binaryDomain_isOpen.mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero matrix)]
      with value invertibility
    exact (realOrbit_inverse_translation data vector.val matrix value invertibility).symm
  have derivativeEquality := (germEquality.iteratedFDeriv ℝ order).eq_of_nhds
  exact derivativeEquality.trans (actionComposition.trans
    (congrArg (fun derivative => action.compContinuousMultilinearMap derivative)
      (composition.trans atIdentity)))

theorem unitaryOperator_norm_le (data : CuspidalRepresentation) (matrix : BinaryAdelicGL) :
    ‖unitaryOperator data matrix‖ ≤ 1 :=
  (data.π matrix).mkContinuous_norm_le zero_le_one _

theorem realOrbit_derivative_norm_le (data : CuspidalRepresentation) (vector : data.smooth)
    (matrix : BinaryRealGL) (order : ℕ) :
    ‖iteratedFDeriv ℝ order (realOrbit data vector.val) matrix.val‖ ≤
      ‖orbitDerivative data order vector.val‖ * ‖leftMultiplication matrix⁻¹.val‖ ^ order := by
  rw [realOrbit_derivative_formula]
  apply (((unitaryOperator data (atInfinity matrix)).restrictScalars ℝ).norm_compContinuousMultilinearMap_le _).trans
  rw [ContinuousLinearMap.norm_restrictScalars]
  apply (mul_le_of_le_one_left (norm_nonneg _) (unitaryOperator_norm_le data _)).trans
  have bound :
      ‖(orbitDerivative data order vector.val).compContinuousLinearMap
        (fun _ => leftMultiplication matrix⁻¹.val)‖ ≤
      ‖orbitDerivative data order vector.val‖ * ∏ _ : Fin order, ‖leftMultiplication matrix⁻¹.val‖ :=
    (orbitDerivative data order vector.val).norm_compContinuousLinearMap_le
      (fun _ => leftMultiplication matrix⁻¹.val)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at bound
  exact bound

noncomputable def leftMultiplicationLinear : BinaryMatrix →ₗ[ℝ] (BinaryMatrix →L[ℝ] BinaryMatrix) where
  toFun := leftMultiplication
  map_add' first second := by
    apply ContinuousLinearMap.ext
    intro value
    exact add_mul first second value
  map_smul' scalar matrix := by
    apply ContinuousLinearMap.ext
    intro value
    exact smul_mul_assoc scalar matrix value

theorem leftMultiplication_continuous : Continuous leftMultiplication :=
  leftMultiplicationLinear.continuous_of_finiteDimensional

theorem inverse_leftMultiplication_continuous :
    Continuous (fun matrix : BinaryRealGL => leftMultiplication matrix⁻¹.val) :=
  leftMultiplication_continuous.comp (Units.continuous_val.comp continuous_inv)

theorem realOrbit_derivative_compact_bound (data : CuspidalRepresentation)
    {compactSet : Set BinaryRealGL} (compactness : IsCompact compactSet) (order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ vector : data.smooth, ∀ matrix ∈ compactSet,
      ‖iteratedFDeriv ℝ order (realOrbit data vector.val) matrix.val‖ ≤
        constant * ‖orbitDerivative data order vector.val‖ := by
  obtain ⟨bound, boundProperty⟩ := compactness.exists_bound_of_continuousOn
    inverse_leftMultiplication_continuous.continuousOn
  let constant := max 0 bound
  have nonnegativeConstant : 0 ≤ constant := le_max_left _ _
  refine ⟨constant ^ order, pow_nonneg nonnegativeConstant order, ?_⟩
  intro vector matrix membership
  have multiplicationBound : ‖leftMultiplication matrix⁻¹.val‖ ≤ constant :=
    (boundProperty matrix membership).trans (le_max_right _ _)
  calc
    _ ≤ ‖orbitDerivative data order vector.val‖ * ‖leftMultiplication matrix⁻¹.val‖ ^ order :=
      realOrbit_derivative_norm_le data vector matrix order
    _ ≤ ‖orbitDerivative data order vector.val‖ * constant ^ order :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) multiplicationBound order) (norm_nonneg _)
    _ = constant ^ order * ‖orbitDerivative data order vector.val‖ := mul_comm _ _

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation
