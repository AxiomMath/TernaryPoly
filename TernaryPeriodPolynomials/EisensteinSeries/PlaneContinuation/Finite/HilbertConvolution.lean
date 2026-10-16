module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.MatrixWeight
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Endpoint.Admissibility

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactAveraging TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteHilbertConvolution

theorem atFinite_continuous : Continuous (atFinite (m := 2)) :=
  BinaryProductHaar.combine_continuous.comp (continuous_const.prodMk continuous_id)

def action (data : CuspidalRepresentation) (binary : BinaryAdelicGL) : data.H →L[ℂ] data.H :=
  (⟨data.π binary, data.unitary binary⟩ : data.H →ₗᵢ[ℂ] data.H).toContinuousLinearMap

theorem integrand_integrable (data : CuspidalRepresentation) (coefficient : BinaryFiniteGL → ℂ)
    (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure) (vector : data.H) :
    Integrable (fun binary => coefficient binary • data.π (atFinite binary) vector) BinaryProductHaar.finiteMeasure := by
  apply (integrable.norm.mul_const ‖vector‖).mono'
    (integrable.aestronglyMeasurable.smul ((data.continuous vector).comp atFinite_continuous).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun binary => by
    change ‖coefficient binary • data.π (atFinite binary) vector‖ ≤ ‖coefficient binary‖ * ‖vector‖
    rw [norm_smul, data.unitary])

def linear (data : CuspidalRepresentation) (coefficient : BinaryFiniteGL → ℂ)
    (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure) : data.H →ₗ[ℂ] data.H where
  toFun vector := ∫ binary, coefficient binary • data.π (atFinite binary) vector ∂BinaryProductHaar.finiteMeasure
  map_add' first second := by
    simp only [map_add, smul_add]
    exact integral_add (integrand_integrable data coefficient integrable first)
      (integrand_integrable data coefficient integrable second)
  map_smul' scalar vector := by
    simp only [map_smul, smul_comm (coefficient _) scalar]
    exact integral_smul scalar _

theorem linear_bound (data : CuspidalRepresentation) (coefficient : BinaryFiniteGL → ℂ)
    (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure) (vector : data.H) :
    ‖linear data coefficient integrable vector‖ ≤
      (∫ binary, ‖coefficient binary‖ ∂BinaryProductHaar.finiteMeasure) * ‖vector‖ := by
  have bound := norm_integral_le_integral_norm
    (μ := BinaryProductHaar.finiteMeasure) (fun binary => coefficient binary • data.π (atFinite binary) vector)
  simpa only [linear, LinearMap.coe_mk, AddHom.coe_mk, norm_smul, data.unitary, integral_mul_const] using bound

def operator (data : CuspidalRepresentation) (coefficient : BinaryFiniteGL → ℂ)
    (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure) : data.H →L[ℂ] data.H :=
  (linear data coefficient integrable).mkContinuous
    (∫ binary, ‖coefficient binary‖ ∂BinaryProductHaar.finiteMeasure) (linear_bound data coefficient integrable)

theorem operator_apply (data : CuspidalRepresentation) (coefficient : BinaryFiniteGL → ℂ)
    (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure) (vector : data.H) :
    operator data coefficient integrable vector =
      ∫ binary, coefficient binary • data.π (atFinite binary) vector ∂BinaryProductHaar.finiteMeasure := rfl

theorem operator_norm (data : CuspidalRepresentation) (coefficient : BinaryFiniteGL → ℂ)
    (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure) :
    ‖operator data coefficient integrable‖ ≤ ∫ binary, ‖coefficient binary‖ ∂BinaryProductHaar.finiteMeasure :=
  ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg (fun _ => norm_nonneg _))
    (linear_bound data coefficient integrable)

theorem operator_sub (data : CuspidalRepresentation) (first second : BinaryFiniteGL → ℂ)
    (firstIntegrable : Integrable first BinaryProductHaar.finiteMeasure)
    (secondIntegrable : Integrable second BinaryProductHaar.finiteMeasure) :
    operator data (first - second) (firstIntegrable.sub secondIntegrable) =
      operator data first firstIntegrable - operator data second secondIntegrable := by
  ext vector
  simp only [operator_apply, Pi.sub_apply, sub_smul, sub_apply]
  exact integral_sub (integrand_integrable data first firstIntegrable vector)
    (integrand_integrable data second secondIntegrable vector)

theorem operator_difference_bound (data : CuspidalRepresentation) (first second : BinaryFiniteGL → ℂ)
    (firstIntegrable : Integrable first BinaryProductHaar.finiteMeasure)
    (secondIntegrable : Integrable second BinaryProductHaar.finiteMeasure) :
    ‖operator data first firstIntegrable - operator data second secondIntegrable‖ ≤
      ∫ binary, ‖first binary - second binary‖ ∂BinaryProductHaar.finiteMeasure := by
  rw [← operator_sub]
  exact operator_norm data (first - second) (firstIntegrable.sub secondIntegrable)

theorem operator_real (data : CuspidalRepresentation) (coefficient : BinaryFiniteGL → ℂ)
    (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure)
    (matrix : BinaryRealGL) (vector : data.H) :
    operator data coefficient integrable (data.π (atInfinity matrix) vector) =
      data.π (atInfinity matrix) (operator data coefficient integrable vector) := by
  rw [operator_apply, operator_apply]
  have commute (binary : BinaryFiniteGL) :
      coefficient binary • data.π (atFinite binary) (data.π (atInfinity matrix) vector) =
        action data (atInfinity matrix) (coefficient binary • data.π (atFinite binary) vector) := by
    change _ = data.π (atInfinity matrix) (coefficient binary • data.π (atFinite binary) vector)
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
      TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.atFinite_atInfinity_commute]
  simp_rw [commute]
  exact (action data (atInfinity matrix)).integral_comp_comm
    (integrand_integrable data coefficient integrable vector)

def projected (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (coefficient : BinaryFiniteGL → ℂ) (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure) :
    data.H →L[ℂ] data.H := (averagingOperator data level).comp (operator data coefficient integrable)

theorem projected_fixed (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (coefficient : BinaryFiniteGL → ℂ) (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure)
    (vector : data.H) : projected data level coefficient integrable vector ∈ fixedSubspace data level :=
  averagingOperator_mem_fixedSubspace data level _

theorem projected_real (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (coefficient : BinaryFiniteGL → ℂ) (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure)
    (matrix : BinaryRealGL) (vector : data.H) :
    projected data level coefficient integrable (data.π (atInfinity matrix) vector) =
      data.π (atInfinity matrix) (projected data level coefficient integrable vector) := by
  simp only [projected, ContinuousLinearMap.comp_apply, operator_real, averagingOperator_real]

theorem projected_smooth (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (coefficient : BinaryFiniteGL → ℂ) (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure)
    (vector : data.smooth) : projected data level coefficient integrable vector.val ∈ data.smooth := by
  apply (fixed_mem_smooth_iff data level openness compactness _
    (projected_fixed data level coefficient integrable vector.val)).mpr
  have sourceSmooth := ((data.smooth_exact vector.val).mp vector.property).1
  have result : Smooth (fun matrices : Fin 1 → BinaryRealGL =>
      projected data level coefficient integrable (data.π (atInfinity (matrices 0)) vector.val)) :=
    ((projected data level coefficient integrable).restrictScalars ℝ).contDiff.comp_contDiffOn sourceSmooth
  simpa only [projected_real] using result

def smoothMap (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (coefficient : BinaryFiniteGL → ℂ) (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure) :
    data.smooth →ₗ[ℂ] data.smooth where
  toFun vector := ⟨projected data level coefficient integrable vector.val,
    projected_smooth data level openness compactness coefficient integrable vector⟩
  map_add' first second := Subtype.ext (map_add (projected data level coefficient integrable) first.val second.val)
  map_smul' scalar vector := Subtype.ext (map_smul (projected data level coefficient integrable) scalar vector.val)

theorem smoothMap_directional (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (coefficient : BinaryFiniteGL → ℂ) (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure)
    (direction : OrbitSmooth.BinaryMatrix) (vector : data.smooth) :
    smoothMap data level openness compactness coefficient integrable
      (AnalyticDifferentiation.directionalOperator data direction vector) =
        AnalyticDifferentiation.directionalOperator data direction
          (smoothMap data level openness compactness coefficient integrable vector) := by
  let bounded := (projected data level coefficient integrable).restrictScalars ℝ
  have equality : OrbitTranslation.realOrbit data
      (smoothMap data level openness compactness coefficient integrable vector).val =
        bounded ∘ OrbitTranslation.realOrbit data vector.val := by
    funext matrix
    exact (projected_real data level coefficient integrable (invertibleMatrix matrix) vector.val).symm
  have differentiability : DifferentiableAt ℝ (OrbitTranslation.realOrbit data vector.val) 1 :=
    (SobolevSeminorms.smooth_orbit_contDiffAt_one data vector).differentiableAt (by simp)
  have derivative := bounded.hasFDerivAt.comp (1 : OrbitSmooth.BinaryMatrix) differentiability.hasFDerivAt
  rw [← equality] at derivative
  apply Subtype.ext
  exact (congrArg (fun linear : OrbitSmooth.BinaryMatrix →L[ℝ] data.H => linear direction) derivative.fderiv).symm

theorem smoothMap_raising (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (coefficient : BinaryFiniteGL → ℂ) (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure)
    (vector : data.smooth) :
    smoothMap data level openness compactness coefficient integrable (LieOperators.raising data vector) =
      LieOperators.raising data (smoothMap data level openness compactness coefficient integrable vector) := by
  simp only [LieOperators.raising, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul,
    LieOperators.diagonalOperator, LieOperators.symmetricOperator, smoothMap_directional]

theorem smoothMap_lowering (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (coefficient : BinaryFiniteGL → ℂ) (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure)
    (vector : data.smooth) :
    smoothMap data level openness compactness coefficient integrable (LieOperators.lowering data vector) =
      LieOperators.lowering data (smoothMap data level openness compactness coefficient integrable vector) := by
  simp only [LieOperators.lowering, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    LieOperators.diagonalOperator, LieOperators.symmetricOperator, smoothMap_directional]

theorem smoothMap_mode (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (coefficient : BinaryFiniteGL → ℂ) (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure)
    (index : ℤ) (vector : fixedMode data level index) :
    smoothMap data level openness compactness coefficient integrable vector.val ∈ fixedMode data level index := by
  apply (mem_fixedMode_iff data level index _).mpr
  refine ⟨projected_fixed data level coefficient integrable vector.val.val, ?_⟩
  have eigen := ((mem_fixedMode_iff data level index vector.val).mp vector.property).2
  intro parameter
  change data.π (atInfinity (TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle.rotation parameter))
    (projected data level coefficient integrable vector.val.val) = _
  rw [← projected_real, eigen, map_smul]
  rfl

def modeMap (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (openness : IsOpen (level : Set BinaryFiniteGL)) (compactness : IsCompact (level : Set BinaryFiniteGL))
    (coefficient : BinaryFiniteGL → ℂ) (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure)
    (index : ℤ) : Module.End ℂ (fixedMode data level index) :=
  ((smoothMap data level openness compactness coefficient integrable).comp (fixedMode data level index).subtype).codRestrict
    (fixedMode data level index) (smoothMap_mode data level openness compactness coefficient integrable index)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteHilbertConvolution
