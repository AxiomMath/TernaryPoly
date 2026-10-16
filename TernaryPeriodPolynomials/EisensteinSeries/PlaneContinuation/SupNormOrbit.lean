module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CentralDifferentiation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization TernaryPeriodPolynomials.PlaneEisensteinContinuation.CentralDifferentiation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationScalarDerivative TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm
open scoped Matrix.Norms.Elementwise NNReal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SupNormOrbit

noncomputable instance matrixOperatorNorm {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target] :
    NormedAddCommGroup (BinaryMatrix →L[ℝ] Target) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable def realizedDifferential (data : CuspidalRepresentation) (vector : data.smooth) :
    BinaryMatrix →L[ℝ] lp (fun _ : BinaryAdelicGL => ℂ) ⊤ :=
  let linear := ((boundedRealization data).restrictScalars ℝ).comp (directionalSmooth data vector)
  ⟨linear, linear.continuous_of_finiteDimensional⟩

theorem realizedDifferential_apply (data : CuspidalRepresentation) (vector : data.smooth)
    (direction : BinaryMatrix) :
    realizedDifferential data vector direction = boundedRealization data (directionalOperator data direction vector) := rfl

theorem scalarMatrixOrbit_differentiableAt (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) (matrix : BinaryRealGL) :
    DifferentiableAt ℝ (scalarMatrixOrbit data point vector) matrix.val :=
  (((scalarMatrixOrbit_contDiffOn data point vector) matrix.val (Matrix.GeneralLinearGroup.det_ne_zero matrix)).contDiffAt
    (binaryDomain_isOpen.mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero matrix))).differentiableAt (by simp)

theorem scalarMatrixOrbit_fderiv_left (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) (matrix : BinaryRealGL) (direction : BinaryMatrix) :
    fderiv ℝ (scalarMatrixOrbit data point vector) matrix.val (matrix.val * direction) =
      scalarDirectional data (point * atInfinity matrix) vector direction := by
  have atProduct : HasFDerivAt (scalarMatrixOrbit data point vector)
      (fderiv ℝ (scalarMatrixOrbit data point vector) matrix.val) (leftMultiplication matrix.val 1) := by
    rw [leftMultiplication_apply, mul_one]
    exact (scalarMatrixOrbit_differentiableAt data point vector matrix).hasFDerivAt
  have derivative := atProduct.comp 1 (leftMultiplication matrix.val).hasFDerivAt
  have germ : scalarMatrixOrbit data (point * atInfinity matrix) vector =ᶠ[nhds (1 : BinaryMatrix)]
      scalarMatrixOrbit data point vector ∘ leftMultiplication matrix.val := by
    filter_upwards [binaryDomain_isOpen.mem_nhds (show (1 : BinaryMatrix) ∈ binaryDomain by simp [binaryDomain])]
      with value invertibility
    change data.realize vector (point * atInfinity matrix * atInfinity (invertibleMatrix value)) =
      data.realize vector (point * atInfinity (invertibleMatrix (matrix.val * value)))
    rw [invertibleMatrix_left_mul matrix value invertibility, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul, mul_assoc]
  have equality := (derivative.congr_of_eventuallyEq germ).fderiv
  exact (congrArg (fun linear : BinaryMatrix →L[ℝ] ℂ => linear direction) equality).symm

theorem scalarMatrixOrbit_fderiv {degree : ℕ} (data : InducingData degree) (point : BinaryAdelicGL)
    (vector : data.cusp.smooth) (matrix : BinaryRealGL) (direction : BinaryMatrix) :
    fderiv ℝ (scalarMatrixOrbit data.cusp point vector) matrix.val direction =
      data.cusp.realize (directionalOperator data.cusp (matrix⁻¹.val * direction) vector)
        (point * atInfinity matrix) := by
  have equality := scalarMatrixOrbit_fderiv_left data.cusp point vector matrix (matrix⁻¹.val * direction)
  have cancellation : matrix.val * (matrix⁻¹.val * direction) = direction := by
    have inverseProduct : matrix.val * matrix⁻¹.val = 1 := matrix.val_inv
    rw [← mul_assoc, inverseProduct, one_mul]
  rw [cancellation, scalarDirectional_eq_realized] at equality
  exact equality

theorem scalarMatrixOrbit_fderiv_norm_le {degree : ℕ} (data : InducingData degree) (point : BinaryAdelicGL)
    (vector : data.cusp.smooth) (matrix : BinaryRealGL) :
    ‖fderiv ℝ (scalarMatrixOrbit data.cusp point vector) matrix.val‖ ≤
      ‖realizedDifferential data.cusp vector‖ * ‖leftMultiplication matrix⁻¹.val‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro direction
  change ‖fderiv ℝ (scalarMatrixOrbit data.cusp point vector) matrix.val direction‖ ≤
    (‖realizedDifferential data.cusp vector‖ * ‖leftMultiplication matrix⁻¹.val‖) * ‖direction‖
  rw [scalarMatrixOrbit_fderiv data point vector matrix direction]
  calc
    _ ≤ cuspSupNorm (directionalOperator data.cusp (matrix⁻¹.val * direction) vector) := realize_le_cuspSupNorm _ _
    _ ≤ ‖realizedDifferential data.cusp vector‖ * ‖matrix⁻¹.val * direction‖ :=
      (realizedDifferential data.cusp vector).le_opNorm _
    _ ≤ ‖realizedDifferential data.cusp vector‖ * (‖leftMultiplication matrix⁻¹.val‖ * ‖direction‖) :=
      mul_le_mul_of_nonneg_left ((leftMultiplication matrix⁻¹.val).le_opNorm direction) (norm_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

theorem leftMultiplication_continuous : Continuous leftMultiplication := by
  apply continuous_clm_apply.mpr
  intro direction
  exact continuous_id.matrix_mul continuous_const

theorem exists_local_inverse_bound (matrix : BinaryRealGL) :
    ∃ radius bound : ℝ, 0 < radius ∧ 0 ≤ bound ∧
      ∀ value ∈ Metric.ball matrix.val radius,
        value ∈ binaryDomain ∧ ‖leftMultiplication value⁻¹‖ ≤ bound := by
  have inverseContinuous : ContinuousAt (fun value : BinaryMatrix => value⁻¹) matrix.val :=
    continuousAt_matrix_inv matrix.val
      (NormedRing.inverse_continuousAt (Units.mk0 matrix.val.det (Matrix.GeneralLinearGroup.det_ne_zero matrix)))
  have normContinuous := (leftMultiplication_continuous.continuousAt.comp inverseContinuous).norm
  have boundNeighborhood : {value : BinaryMatrix | ‖leftMultiplication value⁻¹‖ <
      ‖leftMultiplication matrix.val⁻¹‖ + 1} ∈ nhds matrix.val :=
    normContinuous.eventually (eventually_lt_nhds (lt_add_one _))
  have domainNeighborhood := binaryDomain_isOpen.mem_nhds (Matrix.GeneralLinearGroup.det_ne_zero matrix)
  obtain ⟨radius, positiveRadius, ballSubset⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem domainNeighborhood boundNeighborhood)
  exact ⟨radius, ‖leftMultiplication matrix.val⁻¹‖ + 1, positiveRadius, by positivity,
    fun value membership => ⟨(ballSubset membership).1, (ballSubset membership).2.le⟩⟩

theorem scalarMatrixOrbit_sub_bound {degree : ℕ} (data : InducingData degree)
    (vector : data.cusp.smooth) (center : BinaryRealGL) (radius bound : ℝ)
    (neighborhood : ∀ value ∈ Metric.ball center.val radius,
      value ∈ binaryDomain ∧ ‖leftMultiplication value⁻¹‖ ≤ bound)
    (first second : BinaryMatrix) (firstMem : first ∈ Metric.ball center.val radius)
    (secondMem : second ∈ Metric.ball center.val radius) (point : BinaryAdelicGL) :
    ‖scalarMatrixOrbit data.cusp point vector second - scalarMatrixOrbit data.cusp point vector first‖ ≤
      (‖realizedDifferential data.cusp vector‖ * bound) * ‖second - first‖ := by
  apply (convex_ball center.val radius).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) _ _ firstMem secondMem
  · intro value membership
    exact ((scalarMatrixOrbit_contDiffOn data.cusp point vector value (neighborhood value membership).1).contDiffAt
      (binaryDomain_isOpen.mem_nhds (neighborhood value membership).1)).differentiableAt (by simp)
  · intro value membership
    have estimate := scalarMatrixOrbit_fderiv_norm_le data point vector (invertibleMatrix value)
    rw [Matrix.GeneralLinearGroup.coe_inv, invertibleMatrix_val value (neighborhood value membership).1] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_left (neighborhood value membership).2 (norm_nonneg _))

noncomputable def matrixSupOrbit (data : CuspidalRepresentation) (vector : data.smooth)
    (matrix : BinaryMatrix) : lp (fun _ : BinaryAdelicGL => ℂ) ⊤ :=
  boundedRealization data (smoothTranslate data (invertibleMatrix matrix) vector)

theorem matrixSupOrbit_apply (data : CuspidalRepresentation) (vector : data.smooth)
    (matrix : BinaryMatrix) (point : BinaryAdelicGL) :
    matrixSupOrbit data vector matrix point = scalarMatrixOrbit data point vector matrix :=
  smoothTranslate_realize data (invertibleMatrix matrix) vector point

/-- Real translates are continuous in the full cusp supremum norm. -/
theorem matrixSupOrbit_continuousAt {degree : ℕ} (data : InducingData degree)
    (vector : data.cusp.smooth) (matrix : BinaryRealGL) :
    ContinuousAt (matrixSupOrbit data.cusp vector) matrix.val := by
  obtain ⟨radius, bound, positiveRadius, nonnegativeBound, neighborhood⟩ := exists_local_inverse_bound matrix
  let constant : ℝ≥0 := ⟨‖realizedDifferential data.cusp vector‖ * bound,
    mul_nonneg (norm_nonneg _) nonnegativeBound⟩
  have lipschitz : LipschitzOnWith constant (matrixSupOrbit data.cusp vector) (Metric.ball matrix.val radius) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro first firstMem second secondMem
    rw [dist_eq_norm, dist_eq_norm]
    apply lp.norm_le_of_forall_le'
    intro point
    change ‖matrixSupOrbit data.cusp vector first point - matrixSupOrbit data.cusp vector second point‖ ≤ _
    rw [matrixSupOrbit_apply, matrixSupOrbit_apply]
    exact scalarMatrixOrbit_sub_bound data vector matrix radius bound neighborhood
      second first secondMem firstMem point
  exact lipschitz.continuousOn.continuousAt (Metric.ball_mem_nhds matrix.val positiveRadius)

theorem realSupOrbit_continuous {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth) :
    Continuous (fun matrix : BinaryRealGL => boundedRealization data.cusp (smoothTranslate data.cusp matrix vector)) := by
  apply continuous_iff_continuousAt.mpr
  intro matrix
  have continuity := (matrixSupOrbit_continuousAt data vector matrix).comp Units.continuous_val.continuousAt
  change ContinuousAt (fun value : BinaryRealGL => matrixSupOrbit data.cusp vector value.val) matrix at continuity
  have equality : (fun value : BinaryRealGL => matrixSupOrbit data.cusp vector value.val) =
      (fun value : BinaryRealGL => boundedRealization data.cusp (smoothTranslate data.cusp value vector)) := by
    funext value
    simp only [matrixSupOrbit, invertibleMatrix_units]
  rw [equality] at continuity
  exact continuity

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SupNormOrbit
