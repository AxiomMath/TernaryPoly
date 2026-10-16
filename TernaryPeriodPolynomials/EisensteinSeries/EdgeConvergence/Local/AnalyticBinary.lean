module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.AnalyticCovariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.BinaryCovariance
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Norm

@[expose] public section


/-!
# Equivariance of the local Hilbert standard integral under the real binary group

The group `GL₂(ℝ)`, embedded at the place `∞`, acts on the local coordinates `(ℝ × ℚ₃)²` by the
row action on the two real coordinates and scales the Lebesgue part of `localRadicalMeasure` by
`|det|`. Consequently the local standard integral satisfies the same covariance law under
`lineLevi 1 (atInfinity b)` as the global one (`HilbertBinaryCovariance.value_lineLevi`).
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter Topology
open scoped ENNReal
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

local instance normalizedLocalThreeMeasure_isAddHaarBinary :
    normalizedLocalThreeMeasure.IsAddHaarMeasure :=
  normalizedLocalThreeMeasure_haar

/-- The row action of a real binary matrix on the real coordinates of the local line radical. -/
def localRowAction (matrix : BinaryRealGL) (coordinates : LocalLine × LocalLine) :
    LocalLine × LocalLine :=
  let row := BinaryGaussian.rowAction matrix (coordinates.1.1, coordinates.2.1)
  ((row.1, coordinates.1.2), (row.2, coordinates.2.2))

theorem localRowAction_continuous (matrix : BinaryRealGL) :
    Continuous (localRowAction matrix) := by
  unfold localRowAction BinaryGaussian.rowAction
  fun_prop

/-- The row action of the real group at `∞` on the adeles is the local row action. -/
theorem rowAction_atInfinity_local (matrix : BinaryRealGL) (coordinates : LocalLine × LocalLine) :
    BinaryGaussian.rowAction (atInfinity matrix) (localAdele coordinates.1, localAdele coordinates.2) =
      (localAdele (localRowAction matrix coordinates).1,
        localAdele (localRowAction matrix coordinates).2) := by
  apply Prod.ext
  · apply Prod.ext
    · simp [BinaryGaussian.rowAction, localRowAction, localAdele, atInfinity, combineGL, pairMatrix]
    · simp [BinaryGaussian.rowAction, localRowAction, localAdele, atInfinity, combineGL, pairMatrix]
  · apply Prod.ext
    · simp [BinaryGaussian.rowAction, localRowAction, localAdele, atInfinity, combineGL, pairMatrix]
    · simp [BinaryGaussian.rowAction, localRowAction, localAdele, atInfinity, combineGL, pairMatrix]

/-- The row action of a real binary matrix on `ℝ × ℝ` as a linear map. -/
def realRowLinear (matrix : BinaryRealGL) : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ where
  toFun pair := BinaryGaussian.rowAction matrix pair
  map_add' first second := by
    apply Prod.ext <;> simp [BinaryGaussian.rowAction] <;> ring
  map_smul' scalar pair := by
    apply Prod.ext <;> simp [BinaryGaussian.rowAction] <;> ring

theorem realRowLinear_det (matrix : BinaryRealGL) :
    LinearMap.det (realRowLinear matrix) = matrix.val.det := by
  have entryZeroZero : LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      (realRowLinear matrix) 0 0 = matrix.val 0 0 := by
    simp [LinearMap.toMatrix_apply, realRowLinear, BinaryGaussian.rowAction,
      Module.Basis.coe_finTwoProd_repr]
  have entryZeroOne : LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      (realRowLinear matrix) 0 1 = matrix.val 1 0 := by
    simp [LinearMap.toMatrix_apply, realRowLinear, BinaryGaussian.rowAction,
      Module.Basis.coe_finTwoProd_repr]
  have entryOneZero : LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      (realRowLinear matrix) 1 0 = matrix.val 0 1 := by
    simp [LinearMap.toMatrix_apply, realRowLinear, BinaryGaussian.rowAction,
      Module.Basis.coe_finTwoProd_repr]
  have entryOneOne : LinearMap.toMatrix (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ)
      (realRowLinear matrix) 1 1 = matrix.val 1 1 := by
    simp [LinearMap.toMatrix_apply, realRowLinear, BinaryGaussian.rowAction,
      Module.Basis.coe_finTwoProd_repr]
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two,
    Matrix.det_fin_two, entryZeroZero, entryZeroOne, entryOneZero, entryOneOne]
  ring

theorem localRowAction_measure (matrix : BinaryRealGL) :
    Measure.map (localRowAction matrix) localRadicalMeasure =
      ENNReal.ofReal |matrix.val.det|⁻¹ • localRadicalMeasure := by
  have forward := measurePreserving_prodTranspose (volume : Measure ℝ) normalizedLocalThreeMeasure
    (volume : Measure ℝ) normalizedLocalThreeMeasure
  have backward := measurePreserving_prodTranspose (volume : Measure ℝ) (volume : Measure ℝ)
    normalizedLocalThreeMeasure normalizedLocalThreeMeasure
  have forwardMap : Measure.map (fun pair : LocalLine × LocalLine =>
      ((pair.1.1, pair.2.1), (pair.1.2, pair.2.2))) localRadicalMeasure =
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
        (normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure)) :=
    forward.map_eq
  have backwardMap : Measure.map (fun pair : (ℝ × ℝ) × (ℚ_[3] × ℚ_[3]) =>
      ((pair.1.1, pair.2.1), (pair.1.2, pair.2.2)))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
        (normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure)) = localRadicalMeasure :=
    backward.map_eq
  have determinant : LinearMap.det (realRowLinear matrix) ≠ 0 := by
    rw [realRowLinear_det]
    exact GeneralLinearGroup.det_ne_zero matrix
  have scaled : Measure.map (realRowLinear matrix) (volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal |matrix.val.det|⁻¹ • volume := by
    have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ℝ × ℝ)) determinant
    rw [realRowLinear_det, abs_inv] at this
    exact this
  have linearMeasurable : Measurable (realRowLinear matrix) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have product : ENNReal.ofReal |matrix.val.det|⁻¹ •
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
        (normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure)) =
      Measure.map (Prod.map (realRowLinear matrix) (id : ℚ_[3] × ℚ_[3] → ℚ_[3] × ℚ_[3]))
        (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
          (normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure)) := by
    have := Measure.map_prod_map (volume : Measure (ℝ × ℝ))
      (normalizedLocalThreeMeasure.prod normalizedLocalThreeMeasure) linearMeasurable
      (measurable_id (α := ℚ_[3] × ℚ_[3]))
    rw [scaled, Measure.map_id, Measure.prod_smul_left] at this
    exact this
  have middleMeasurable : Measurable (Prod.map (realRowLinear matrix)
      (id : ℚ_[3] × ℚ_[3] → ℚ_[3] × ℚ_[3])) := linearMeasurable.prodMap measurable_id
  have composition : localRowAction matrix =
      (fun pair : (ℝ × ℝ) × (ℚ_[3] × ℚ_[3]) => ((pair.1.1, pair.2.1), (pair.1.2, pair.2.2))) ∘
        (Prod.map (realRowLinear matrix) (id : ℚ_[3] × ℚ_[3] → ℚ_[3] × ℚ_[3])) ∘
        (fun pair : LocalLine × LocalLine => ((pair.1.1, pair.2.1), (pair.1.2, pair.2.2))) := by
    funext pair
    rfl
  calc
    _ = Measure.map (fun pair : (ℝ × ℝ) × (ℚ_[3] × ℚ_[3]) =>
          ((pair.1.1, pair.2.1), (pair.1.2, pair.2.2)))
        (Measure.map (Prod.map (realRowLinear matrix) (id : ℚ_[3] × ℚ_[3] → ℚ_[3] × ℚ_[3]))
          (Measure.map (fun pair : LocalLine × LocalLine =>
            ((pair.1.1, pair.2.1), (pair.1.2, pair.2.2))) localRadicalMeasure)) := by
      rw [Measure.map_map middleMeasurable forward.measurable,
        Measure.map_map backward.measurable (middleMeasurable.comp forward.measurable),
        composition]
    _ = _ := by
      rw [forwardMap, ← product, Measure.map_smul _ backward.measurable.aemeasurable, backwardMap]

theorem integral_localRowAction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (matrix : BinaryRealGL) (function : LocalLine × LocalLine → E)
    (continuous : Continuous function) :
    |matrix.val.det| • (∫ coordinates, function (localRowAction matrix coordinates)
      ∂localRadicalMeasure) = ∫ coordinates, function coordinates ∂localRadicalMeasure := by
  have nonzero : matrix.val.det ≠ 0 := GeneralLinearGroup.det_ne_zero matrix
  have mapped := integral_map (μ := localRadicalMeasure)
    (localRowAction_continuous matrix).measurable.aemeasurable
    (f := function) (by
      rw [localRowAction_measure]
      exact (continuous.aestronglyMeasurable).smul_measure _)
  rw [localRowAction_measure, integral_smul_measure] at mapped
  rw [← mapped, ENNReal.toReal_ofReal (by positivity), smul_smul,
    mul_inv_cancel₀ (abs_ne_zero.mpr nonzero), one_smul]

theorem localIntegrand_eq_integrand {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (coordinates : LocalLine × LocalLine) :
    localIntegrand data parameter function induced argument coordinates =
      HilbertStandard.integrand data parameter function induced argument
        (localAdele coordinates.1, localAdele coordinates.2) :=
  rfl

theorem localIntegrand_lineLevi_real {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (matrix : BinaryRealGL) (argument : AdelicGL) (coordinates : LocalLine × LocalLine) :
    localIntegrand data parameter function induced (lineLevi 1 (atInfinity matrix) * argument)
        coordinates =
      normPower (Matrix.GeneralLinearGroup.det (atInfinity matrix))
        (binaryInductionExponent degree .plane parameter) •
        data.cusp.π (atInfinity matrix)
          (localIntegrand data parameter function induced argument
            (localRowAction matrix coordinates)) := by
  rw [localIntegrand_eq_integrand, HilbertBinaryCovariance.integrand_lineLevi,
    rowAction_atInfinity_local]
  rfl

theorem localValue_lineLevi_real_raw {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (matrix : BinaryRealGL) (argument : AdelicGL) :
    |matrix.val.det| •
      localValue data parameter function induced (lineLevi 1 (atInfinity matrix) * argument) =
      normPower (Matrix.GeneralLinearGroup.det (atInfinity matrix))
        (binaryInductionExponent degree .plane parameter) •
        data.cusp.π (atInfinity matrix) (localValue data parameter function induced argument) := by
  let transformed : LocalLine × LocalLine → data.cusp.H := fun coordinates =>
    localIntegrand data parameter function induced argument (localRowAction matrix coordinates)
  have commute : (∫ coordinates, data.cusp.π (atInfinity matrix) (transformed coordinates)
      ∂localRadicalMeasure) =
      data.cusp.π (atInfinity matrix) (∫ coordinates, transformed coordinates
        ∂localRadicalMeasure) :=
    (CuspHilbertAction.isometry data.cusp (atInfinity matrix)).integral_comp_comm transformed
  have scaled := integral_localRowAction matrix
    (localIntegrand data parameter function induced argument)
    (localIntegrand_continuous data parameter function induced argument)
  change |matrix.val.det| • (∫ coordinates, transformed coordinates ∂localRadicalMeasure) =
    localValue data parameter function induced argument at scaled
  unfold localValue
  simp_rw [localIntegrand_lineLevi_real]
  rw [integral_smul, commute]
  rw [← IsScalarTower.algebraMap_smul (R := ℝ) ℂ]
  rw [smul_comm, ← map_smul, IsScalarTower.algebraMap_smul (R := ℝ) ℂ, scaled]
  rfl

/-- The local standard integral is equivariant under the real binary group. -/
theorem localValue_lineLevi_real {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (matrix : BinaryRealGL) (argument : AdelicGL) :
    localValue data parameter function induced (lineLevi 1 (atInfinity matrix) * argument) =
      normPower (Matrix.GeneralLinearGroup.det (atInfinity matrix))
        (binaryInductionExponent degree .line parameter) •
        data.cusp.π (atInfinity matrix) (localValue data parameter function induced argument) := by
  have positive : (0 : ℝ) < |matrix.val.det| :=
    abs_pos.mpr (GeneralLinearGroup.det_ne_zero matrix)
  apply smul_right_injective data.cusp.H positive.ne'
  change |matrix.val.det| •
      localValue data parameter function induced (lineLevi 1 (atInfinity matrix) * argument) =
    |matrix.val.det| • (normPower (Matrix.GeneralLinearGroup.det (atInfinity matrix))
        (binaryInductionExponent degree .line parameter) •
        data.cusp.π (atInfinity matrix) (localValue data parameter function induced argument))
  rw [localValue_lineLevi_real_raw data parameter function induced matrix argument,
    ← PlaneEisensteinContinuation.Norm.adeleNorm_det_atInfinity matrix,
    ← IsScalarTower.algebraMap_smul (R := ℝ) ℂ, smul_smul,
    HilbertBinaryCovariance.binaryExponent_shift, NormPower.normPower_add,
    HilbertBinaryCovariance.normPower_one_unit, Complex.coe_algebraMap, mul_comm]

end TernaryPeriodPolynomials.EdgeConvergence
