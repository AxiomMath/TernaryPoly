module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.BoundedFamilies
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.MultilinearContinuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticStages
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel
open scoped Matrix.Norms.Elementwise NNReal

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.StageTranslation

noncomputable instance conjugationOperatorNormedSpace : NormedSpace ℝ (BinaryMatrix →L[ℝ] BinaryMatrix) :=
  ContinuousLinearMap.toNormedSpace

theorem atInfinity_continuous {size : ℕ} :
    Continuous (atInfinity (m := size)) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    change Continuous (fun matrix : Matrix.GeneralLinearGroup (Fin size) ℝ =>
      (matrix.val row column, (1 : Matrix (Fin size) (Fin size) FiniteAdeles) row column))
    have values : Continuous (fun matrix : Matrix.GeneralLinearGroup (Fin size) ℝ => matrix.val) :=
      Units.continuous_val
    exact ((continuous_apply column).comp ((continuous_apply row).comp values)).prodMk continuous_const
  · apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    change Continuous (fun matrix : Matrix.GeneralLinearGroup (Fin size) ℝ =>
      (matrix⁻¹.val row column, (1 : Matrix (Fin size) (Fin size) FiniteAdeles) row column))
    have values : Continuous (fun matrix : Matrix.GeneralLinearGroup (Fin size) ℝ => matrix⁻¹.val) :=
      Units.continuous_val.comp continuous_inv
    exact ((continuous_apply column).comp ((continuous_apply row).comp values)).prodMk continuous_const

noncomputable def conjugation (matrix : BinaryRealGL) : BinaryMatrix →L[ℝ] BinaryMatrix :=
  ⟨(LinearMap.mulRight ℝ matrix.val).comp (LinearMap.mulLeft ℝ matrix⁻¹.val),
    ((LinearMap.mulRight ℝ matrix.val).comp (LinearMap.mulLeft ℝ matrix⁻¹.val)).continuous_of_finiteDimensional⟩

theorem conjugation_apply (matrix : BinaryRealGL) (value : BinaryMatrix) :
    conjugation matrix value = matrix⁻¹.val * value * matrix.val := rfl

theorem conjugation_one (matrix : BinaryRealGL) : conjugation matrix 1 = 1 := by
  change matrix⁻¹.val * 1 * matrix.val = 1
  rw [mul_one]
  exact matrix.inv_val

theorem conjugation_continuous : Continuous conjugation := by
  apply continuous_clm_apply.mpr
  intro value
  have inverseContinuous : Continuous (fun matrix : BinaryRealGL => matrix⁻¹.val) :=
    Units.continuous_val.comp continuous_inv
  exact (inverseContinuous.matrix_mul continuous_const).matrix_mul Units.continuous_val

theorem conjugation_det (matrix : BinaryRealGL) (value : BinaryMatrix) :
    (conjugation matrix value).det = value.det := by
  have cancellation : matrix⁻¹.val.det * matrix.val.det = 1 := by
    rw [← Matrix.det_mul]
    exact (congrArg Matrix.det (show matrix⁻¹.val * matrix.val = 1 from matrix.inv_val)).trans Matrix.det_one
  change (matrix⁻¹.val * value * matrix.val).det = value.det
  simp only [Matrix.det_mul]
  calc
    _ = value.det * (matrix⁻¹.val.det * matrix.val.det) := by ring
    _ = value.det := by rw [cancellation, mul_one]

theorem invertibleMatrix_conjugation (matrix : BinaryRealGL) (value : BinaryMatrix) :
    invertibleMatrix (conjugation matrix value) = matrix⁻¹ * invertibleMatrix value * matrix := by
  by_cases invertibility : value.det ≠ 0
  · apply Units.ext
    rw [invertibleMatrix_val _ (by simpa only [conjugation_det] using invertibility),
      Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      invertibleMatrix_val _ invertibility]
    rfl
  · simp only [invertibleMatrix, conjugation_det, dite_eq_right invertibility, mul_one, inv_mul_cancel]

theorem realOrbit_translate (data : CuspidalRepresentation) (vector : data.H)
    (matrix : BinaryRealGL) (value : BinaryMatrix) :
    realOrbit data (data.π (atInfinity matrix) vector) value =
      data.π (atInfinity matrix) (realOrbit data vector (conjugation matrix value)) := by
  unfold realOrbit
  rw [invertibleMatrix_conjugation, ← Module.End.mul_apply, ← map_mul,
    ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul, ← Module.End.mul_apply, ← map_mul,
    ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul]
  congr 2
  group

noncomputable def translateCoefficient (data : CuspidalRepresentation) (order : ℕ)
    (coefficient : ContinuousMultilinearMap ℝ (fun _ : Fin order => BinaryMatrix) data.H)
    (scale : ℝ) (matrix : BinaryRealGL) :
    ContinuousMultilinearMap ℝ (fun _ : Fin order => BinaryMatrix) data.H :=
  (((unitaryOperator data (atInfinity matrix)).restrictScalars ℝ).compContinuousMultilinearMap coefficient).compContinuousLinearMap
    (fun _ => scale • conjugation matrix)

theorem translateCoefficient_apply (data : CuspidalRepresentation) (order : ℕ)
    (coefficient : ContinuousMultilinearMap ℝ (fun _ : Fin order => BinaryMatrix) data.H)
    (scale : ℝ) (matrix : BinaryRealGL) (directions : Fin order → BinaryMatrix) :
    translateCoefficient data order coefficient scale matrix directions =
      data.π (atInfinity matrix) (coefficient (fun index => scale • conjugation matrix (directions index))) := rfl

theorem translateCoefficient_continuous (data : CuspidalRepresentation) (order : ℕ)
    (coefficient : ContinuousMultilinearMap ℝ (fun _ : Fin order => BinaryMatrix) data.H)
    (scale : ℝ) : Continuous (translateCoefficient data order coefficient scale) := by
  have postContinuous : Continuous (fun matrix : BinaryRealGL =>
      ((unitaryOperator data (atInfinity matrix)).restrictScalars ℝ).compContinuousMultilinearMap coefficient) := by
    apply TernaryPeriodPolynomials.PlaneEisensteinContinuation.MultilinearContinuity.continuous_of_eval
    intro directions
    exact (data.continuous (coefficient directions)).comp atInfinity_continuous
  have preContinuous : Continuous (fun matrix : BinaryRealGL =>
      fun _ : Fin order => scale • conjugation matrix) :=
    continuous_pi (fun _ => conjugation_continuous.const_smul scale)
  exact ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin order => BinaryMatrix) (fun _ : Fin order => BinaryMatrix) data.H).coe_continuous.comp
      preContinuous).clm_apply postContinuous

theorem translateCoefficient_norm_le (data : CuspidalRepresentation) (order : ℕ)
    (coefficient : ContinuousMultilinearMap ℝ (fun _ : Fin order => BinaryMatrix) data.H)
    (scale : ℝ) (matrix : BinaryRealGL) :
    ‖translateCoefficient data order coefficient scale matrix‖ ≤
      ‖coefficient‖ * ‖scale • conjugation matrix‖ ^ order := by
  have postBound :
      ‖((unitaryOperator data (atInfinity matrix)).restrictScalars ℝ).compContinuousMultilinearMap coefficient‖ ≤
        ‖coefficient‖ := by
    apply (((unitaryOperator data (atInfinity matrix)).restrictScalars ℝ).norm_compContinuousMultilinearMap_le _).trans
    rw [ContinuousLinearMap.norm_restrictScalars]
    exact mul_le_of_le_one_left (norm_nonneg _) (unitaryOperator_norm_le data _)
  have preBound :=
    (((unitaryOperator data (atInfinity matrix)).restrictScalars ℝ).compContinuousMultilinearMap coefficient).norm_compContinuousLinearMap_le
      (fun _ : Fin order => scale • conjugation matrix)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at preBound
  exact preBound.trans (mul_le_mul_of_nonneg_right postBound (pow_nonneg (norm_nonneg _) order))

theorem translateCoefficient_half_bound (data : CuspidalRepresentation) (coefficients : CoefficientSpace data)
    (scale : ℝ) (matrix : BinaryRealGL) (contraction : ‖scale • conjugation matrix‖ ≤ 1 / 2) (order : ℕ) :
    ‖translateCoefficient data order (coefficients order) scale matrix‖ ≤ ‖coefficients‖ * (1 / 2 : ℝ) ^ order := by
  apply (translateCoefficient_norm_le data order (coefficients order) scale matrix).trans
  exact mul_le_mul (lp.norm_apply_le_norm (by simp) coefficients order)
    (pow_le_pow_left₀ (norm_nonneg _) contraction order) (pow_nonneg (norm_nonneg _) order) (norm_nonneg _)

noncomputable def translationCoefficients (data : CuspidalRepresentation) (coefficients : CoefficientSpace data)
    (scale : ℝ) (domain : Set BinaryRealGL)
    (contraction : ∀ matrix ∈ domain, ‖scale • conjugation matrix‖ ≤ 1 / 2) (matrix : domain) :
    CoefficientSpace data :=
  ⟨fun order => translateCoefficient data order (coefficients order) scale matrix.val,
    memℓp_infty (by
      refine ⟨‖coefficients‖, ?_⟩
      rintro value ⟨order, rfl⟩
      exact (translateCoefficient_half_bound data coefficients scale matrix.val
        (contraction matrix.val matrix.property) order).trans
        (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num))))⟩

theorem translationCoefficients_apply (data : CuspidalRepresentation) (coefficients : CoefficientSpace data)
    (scale : ℝ) (domain : Set BinaryRealGL)
    (contraction : ∀ matrix ∈ domain, ‖scale • conjugation matrix‖ ≤ 1 / 2) (matrix : domain) (order : ℕ) :
    translationCoefficients data coefficients scale domain contraction matrix order =
      translateCoefficient data order (coefficients order) scale matrix.val := rfl

theorem translationCoefficients_norm_le (data : CuspidalRepresentation) (coefficients : CoefficientSpace data)
    (scale : ℝ) (domain : Set BinaryRealGL)
    (contraction : ∀ matrix ∈ domain, ‖scale • conjugation matrix‖ ≤ 1 / 2) (matrix : domain) :
    ‖translationCoefficients data coefficients scale domain contraction matrix‖ ≤ ‖coefficients‖ := by
  apply lp.norm_le_of_forall_le'
  intro order
  exact (translateCoefficient_half_bound data coefficients scale matrix.val
    (contraction matrix.val matrix.property) order).trans
    (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (by norm_num) (by norm_num)))

theorem translationCoefficients_continuous (data : CuspidalRepresentation) (coefficients : CoefficientSpace data)
    (scale : ℝ) (domain : Set BinaryRealGL)
    (contraction : ∀ matrix ∈ domain, ‖scale • conjugation matrix‖ ≤ 1 / 2) :
    Continuous (translationCoefficients data coefficients scale domain contraction) := by
  apply continuousOn_univ.mp
  refine @TernaryPeriodPolynomials.PlaneEisensteinContinuation.BoundedFamilies.continuousOn_of_summable_bound ℕ domain
    (fun order => ContinuousMultilinearMap ℝ (fun _ : Fin order => BinaryMatrix) data.H) _
    (fun order => binaryMultilinearNorm (order := order) (Target := data.H))
    (fun _ => inferInstance) (TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticLimits.binaryMultilinearComplete data)
    (translationCoefficients data coefficients scale domain contraction) Set.univ ?_
    (fun order => ‖coefficients‖ * (1 / 2 : ℝ) ^ order) ?_ ?_
  · intro order
    exact ((translateCoefficient_continuous data order (coefficients order) scale).comp continuous_subtype_val).continuousOn
  · exact (summable_geometric_of_norm_lt_one (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)).mul_left ‖coefficients‖
  · intro matrix _ order
    exact translateCoefficient_half_bound data coefficients scale matrix.val
      (contraction matrix.val matrix.property) order

theorem weighted_translationCoefficients (data : CuspidalRepresentation) (coefficients : CoefficientSpace data)
    (radius smallerRadius : ℝ≥0) (positiveSmaller : 0 < smallerRadius) (domain : Set BinaryRealGL)
    (contraction : ∀ matrix ∈ domain, ‖((smallerRadius : ℝ) / radius) • conjugation matrix‖ ≤ 1 / 2)
    (matrix : domain) (order : ℕ) (directions : Fin order → BinaryMatrix) :
    weightedSeries data smallerRadius
        (translationCoefficients data coefficients ((smallerRadius : ℝ) / radius) domain contraction matrix)
        order directions =
      data.π (atInfinity matrix.val)
        (weightedSeries data radius coefficients order (fun index => conjugation matrix.val (directions index))) := by
  let action := (unitaryOperator data (atInfinity matrix.val)).restrictScalars ℝ
  change ((smallerRadius : ℝ)⁻¹ ^ order) •
      action (coefficients order (fun index => ((smallerRadius : ℝ) / radius) • conjugation matrix.val (directions index))) =
    action (((radius : ℝ)⁻¹ ^ order) • coefficients order (fun index => conjugation matrix.val (directions index)))
  rw [← action.map_smul, (coefficients order).map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_smul, ← mul_pow]
  have nonzeroSmaller : (smallerRadius : ℝ) ≠ 0 := by exact_mod_cast positiveSmaller.ne'
  rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ nonzeroSmaller, one_mul]

theorem conjugation_ball (radius smallerRadius : ℝ≥0) (positiveRadius : 0 < radius)
    (matrix : BinaryRealGL)
    (contraction : ‖((smallerRadius : ℝ) / radius) • conjugation matrix‖ ≤ 1 / 2)
    {offset : BinaryMatrix} (membership : offset ∈ Metric.eball 0 ((smallerRadius / 2 : ℝ≥0) : ENNReal)) :
    conjugation matrix offset ∈ Metric.eball 0 ((radius / 2 : ℝ≥0) : ENNReal) := by
  have positiveRealRadius : (0 : ℝ) < radius := by exact_mod_cast positiveRadius
  have offsetNNBound : ‖offset‖₊ < smallerRadius / 2 := by
    simpa only [Metric.mem_eball, edist_nndist, nndist_zero_right, ENNReal.coe_lt_coe] using membership
  have offsetBound : ‖offset‖ < (smallerRadius : ℝ) / 2 := by exact_mod_cast offsetNNBound
  have scaleNorm : ‖((smallerRadius : ℝ) / radius) • conjugation matrix‖ =
      ((smallerRadius : ℝ) / radius) * ‖conjugation matrix‖ :=
    (norm_smul _ _).trans (congrArg (fun value : ℝ => value * ‖conjugation matrix‖)
      (Real.norm_of_nonneg (div_nonneg smallerRadius.property radius.property)))
  have scaledBound := scaleNorm.symm.le.trans contraction
  rw [div_mul_eq_mul_div] at scaledBound
  have operatorBound : (smallerRadius : ℝ) * ‖conjugation matrix‖ ≤ 1 / 2 * (radius : ℝ) :=
    (div_le_iff₀ positiveRealRadius).mp scaledBound
  have productBound : ‖conjugation matrix‖ * ‖offset‖ ≤ ‖conjugation matrix‖ * ((smallerRadius : ℝ) / 2) :=
    mul_le_mul_of_nonneg_left offsetBound.le (norm_nonneg (conjugation matrix))
  have vectorBound : ‖conjugation matrix offset‖ ≤ ‖conjugation matrix‖ * ‖offset‖ :=
    (conjugation matrix).le_opNorm offset
  have result : ‖conjugation matrix offset‖ < (radius : ℝ) / 2 := by nlinarith
  have resultNN : ‖conjugation matrix offset‖₊ < radius / 2 := by exact_mod_cast result
  simpa only [Metric.mem_eball, edist_nndist, nndist_zero_right, ENNReal.coe_lt_coe] using resultNN

theorem translated_expansion (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (radius smallerRadius : ℝ≥0) (positiveRadius : 0 < radius) (positiveSmaller : 0 < smallerRadius)
    (domain : Set BinaryRealGL)
    (contraction : ∀ matrix ∈ domain, ‖((smallerRadius : ℝ) / radius) • conjugation matrix‖ ≤ 1 / 2)
    (element : analyticStage data level radius positiveRadius) (matrix : domain) :
    HasFPowerSeriesOnBall (realOrbit data (data.π (atInfinity matrix.val) element.val.1))
      (weightedSeries data smallerRadius
        (translationCoefficients data element.val.2 ((smallerRadius : ℝ) / radius) domain contraction matrix))
      1 ((smallerRadius / 2 : ℝ≥0) : ENNReal) := by
  have halfLe : ((smallerRadius / 2 : ℝ≥0) : ENNReal) ≤ (smallerRadius : ENNReal) := by
    exact_mod_cast (div_le_self (show (0 : ℝ≥0) ≤ smallerRadius from zero_le) (show (1 : ℝ≥0) ≤ 2 by norm_num))
  refine ⟨halfLe.trans (weightedSeries_radius_ge data smallerRadius positiveSmaller _),
    halfRadius_pos smallerRadius positiveSmaller, ?_⟩
  intro offset membership
  have transformedMembership := conjugation_ball radius smallerRadius positiveRadius matrix.val
    (contraction matrix.val matrix.property) membership
  let action := (unitaryOperator data (atInfinity matrix.val)).restrictScalars ℝ
  have mappedSum := action.hasSum (element.property.2.hasSum transformedMembership)
  have termEquality : (fun order => weightedSeries data smallerRadius
        (translationCoefficients data element.val.2 ((smallerRadius : ℝ) / radius) domain contraction matrix)
        order (fun _ => offset)) =
      (fun order => action (weightedSeries data radius element.val.2 order (fun _ => conjugation matrix.val offset))) := by
    funext order
    exact weighted_translationCoefficients data element.val.2 radius smallerRadius positiveSmaller
      domain contraction matrix order (fun _ => offset)
  have totalEquality : action (realOrbit data element.val.1 (1 + conjugation matrix.val offset)) =
      realOrbit data (data.π (atInfinity matrix.val) element.val.1) (1 + offset) := by
    rw [realOrbit_translate, map_add, conjugation_one]
    rfl
  apply (congrArg (fun summand : ℕ → data.H =>
    HasSum summand (realOrbit data (data.π (atInfinity matrix.val) element.val.1) (1 + offset))) termEquality).mpr
  exact (congrArg (fun total : data.H =>
    HasSum (fun order => action (weightedSeries data radius element.val.2 order
      (fun _ => conjugation matrix.val offset))) total) totalEquality).mp mappedSum

noncomputable def translatedStageFamily (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (radius smallerRadius : ℝ≥0) (positiveRadius : 0 < radius) (positiveSmaller : 0 < smallerRadius)
    (domain : Set BinaryRealGL)
    (contraction : ∀ matrix ∈ domain, ‖((smallerRadius : ℝ) / radius) • conjugation matrix‖ ≤ 1 / 2)
    (element : analyticStage data level radius positiveRadius) (matrix : domain) :
    analyticStage data level smallerRadius positiveSmaller :=
  ⟨(data.π (atInfinity matrix.val) element.val.1,
    translationCoefficients data element.val.2 ((smallerRadius : ℝ) / radius) domain contraction matrix),
    fixedSubspace_real_stable data level matrix.val element.val.1 element.property.1,
    translated_expansion data level radius smallerRadius positiveRadius positiveSmaller domain contraction element matrix⟩

theorem translatedStageFamily_continuous (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (radius smallerRadius : ℝ≥0) (positiveRadius : 0 < radius) (positiveSmaller : 0 < smallerRadius)
    (domain : Set BinaryRealGL)
    (contraction : ∀ matrix ∈ domain, ‖((smallerRadius : ℝ) / radius) • conjugation matrix‖ ≤ 1 / 2)
    (element : analyticStage data level radius positiveRadius) :
    Continuous (translatedStageFamily data level radius smallerRadius positiveRadius positiveSmaller domain contraction element) :=
  ((((data.continuous element.val.1).comp atInfinity_continuous).comp continuous_subtype_val).prodMk
    (translationCoefficients_continuous data element.val.2 ((smallerRadius : ℝ) / radius) domain contraction)).subtype_mk _

theorem stageHilbertMap_translatedStageFamily (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (radius smallerRadius : ℝ≥0) (positiveRadius : 0 < radius) (positiveSmaller : 0 < smallerRadius)
    (domain : Set BinaryRealGL)
    (contraction : ∀ matrix ∈ domain, ‖((smallerRadius : ℝ) / radius) • conjugation matrix‖ ≤ 1 / 2)
    (element : analyticStage data level radius positiveRadius) (matrix : domain) :
    stageHilbertMap data level smallerRadius positiveSmaller
      (translatedStageFamily data level radius smallerRadius positiveRadius positiveSmaller domain contraction element matrix) =
      data.π (atInfinity matrix.val) (stageHilbertMap data level radius positiveRadius element) := rfl

theorem translatedStageFamily_norm_le (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (radius smallerRadius : ℝ≥0) (positiveRadius : 0 < radius) (positiveSmaller : 0 < smallerRadius)
    (domain : Set BinaryRealGL)
    (contraction : ∀ matrix ∈ domain, ‖((smallerRadius : ℝ) / radius) • conjugation matrix‖ ≤ 1 / 2)
    (element : analyticStage data level radius positiveRadius) (matrix : domain) :
    ‖translatedStageFamily data level radius smallerRadius positiveRadius positiveSmaller domain contraction element matrix‖ ≤
      ‖element‖ := by
  change max ‖data.π (atInfinity matrix.val) element.val.1‖
    ‖translationCoefficients data element.val.2 ((smallerRadius : ℝ) / radius) domain contraction matrix‖ ≤
      max ‖element.val.1‖ ‖element.val.2‖
  exact max_le_max (data.unitary _ _).le
    (translationCoefficients_norm_le data element.val.2 ((smallerRadius : ℝ) / radius) domain contraction matrix)

theorem exists_compact_contraction (radius : ℝ≥0) (positiveRadius : 0 < radius)
    {compactSet : Set BinaryRealGL} (compactness : IsCompact compactSet) :
    ∃ smallerRadius : ℝ≥0, 0 < smallerRadius ∧
      ∀ matrix ∈ compactSet, ‖((smallerRadius : ℝ) / radius) • conjugation matrix‖ ≤ 1 / 2 := by
  obtain ⟨bound, boundProperty⟩ := compactness.exists_bound_of_continuousOn conjugation_continuous.continuousOn
  let constant : ℝ≥0 := ⟨max 1 bound, le_trans zero_le_one (le_max_left _ _)⟩
  have positiveConstant : (0 : ℝ) < constant := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have constantPositive : (0 : ℝ≥0) < constant := by exact_mod_cast positiveConstant
  let smallerRadius : ℝ≥0 := radius / (2 * constant)
  have positiveSmaller : 0 < smallerRadius := div_pos positiveRadius (mul_pos (by norm_num) constantPositive)
  have positiveRealRadius : (0 : ℝ) < radius := by exact_mod_cast positiveRadius
  have ratioEquality : (smallerRadius : ℝ) / radius = 1 / (2 * (constant : ℝ)) := by
    dsimp [smallerRadius]
    field_simp
  refine ⟨smallerRadius, positiveSmaller, ?_⟩
  intro matrix membership
  have matrixBound : ‖conjugation matrix‖ ≤ (constant : ℝ) :=
    (boundProperty matrix membership).trans (le_max_right _ _)
  have ratioNonnegative : 0 ≤ (smallerRadius : ℝ) / radius := div_nonneg smallerRadius.property radius.property
  calc
    _ = ((smallerRadius : ℝ) / radius) * ‖conjugation matrix‖ :=
      (norm_smul _ _).trans (congrArg (fun value : ℝ => value * ‖conjugation matrix‖)
        (Real.norm_of_nonneg ratioNonnegative))
    _ ≤ ((smallerRadius : ℝ) / radius) * constant := mul_le_mul_of_nonneg_left matrixBound ratioNonnegative
    _ = 1 / 2 := by rw [ratioEquality]; field_simp

theorem exists_compactStageFamily (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactLevel : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) (fixed : vector.val ∈ fixedSubspace data level)
    {compactSet : Set BinaryRealGL} (compactness : IsCompact compactSet) :
    ∃ radius : ℝ≥0, ∃ positiveRadius : 0 < radius,
      ∃ family : compactSet → analyticStage data level radius positiveRadius,
        Continuous family ∧ ∀ matrix,
          stageHilbertMap data level radius positiveRadius (family matrix) =
            data.π (atInfinity matrix.val) vector.val := by
  obtain ⟨radius, positiveRadius, element, vectorEquality⟩ :=
    (mem_smooth_iff_exists_stage data level openness compactLevel vector.val fixed).mp vector.property
  obtain ⟨smallerRadius, positiveSmaller, contraction⟩ := exists_compact_contraction radius positiveRadius compactness
  refine ⟨smallerRadius, positiveSmaller,
    translatedStageFamily data level radius smallerRadius positiveRadius positiveSmaller compactSet contraction element,
    translatedStageFamily_continuous data level radius smallerRadius positiveRadius positiveSmaller compactSet contraction element, ?_⟩
  intro matrix
  exact (stageHilbertMap_translatedStageFamily data level radius smallerRadius positiveRadius positiveSmaller
    compactSet contraction element matrix).trans (congrArg (data.π (atInfinity matrix.val)) vectorEquality)

theorem exists_compactParameterStageFamily {Parameter : Type} [TopologicalSpace Parameter] [CompactSpace Parameter]
    (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactLevel : IsCompact (level : Set BinaryFiniteGL))
    (vector : data.smooth) (fixed : vector.val ∈ fixedSubspace data level)
    (matrices : Parameter → BinaryRealGL) (continuousMatrices : Continuous matrices) :
    ∃ radius : ℝ≥0, ∃ positiveRadius : 0 < radius,
      ∃ family : Parameter → analyticStage data level radius positiveRadius,
        Continuous family ∧ ∀ parameter,
          stageHilbertMap data level radius positiveRadius (family parameter) =
            data.π (atInfinity (matrices parameter)) vector.val := by
  obtain ⟨radius, positiveRadius, family, continuousFamily, familyValue⟩ :=
    exists_compactStageFamily data level openness compactLevel vector fixed (isCompact_range continuousMatrices)
  let rangeMap : Parameter → Set.range matrices := fun parameter => ⟨matrices parameter, Set.mem_range_self parameter⟩
  have continuousRange : Continuous rangeMap := continuousMatrices.subtype_mk _
  exact ⟨radius, positiveRadius, family ∘ rangeMap, continuousFamily.comp continuousRange,
    fun parameter => familyValue (rangeMap parameter)⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.StageTranslation
