module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ProjectedCoefficientIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteHilbertConvolution
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationFourier TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationScalarSeries
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ProjectedCoefficientIntegral

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothCoefficientIntegral

theorem modeVector_commute (data : CuspidalRepresentation) (linear : data.H →L[ℂ] data.H)
    (commute : ∀ (matrix : BinaryRealGL) (vector : data.H),
      linear (data.π (atInfinity matrix) vector) = data.π (atInfinity matrix) (linear vector))
    (index : ℤ) (vector : data.H) :
    modeVector data index (linear vector) = linear (modeVector data index vector) := by
  unfold modeVector fourierCoeff
  simp_rw [← commute, ← linear.map_smul]
  exact linear.integral_comp_comm (weighted_orbit_integrable data vector index)

theorem smoothMap_modeProjection (data : CuspidalRepresentation) (coefficient : BinaryFiniteGL → ℂ)
    (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure) (index : ℤ) (vector : data.smooth) :
    smoothMode data index (smoothMap data finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact
      coefficient integrable vector) =
        smoothMap data finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact
          coefficient integrable (smoothMode data index vector) := by
  apply Subtype.ext
  exact modeVector_commute data (projected data finiteCongruence coefficient integrable)
    (projected_real data finiteCongruence coefficient integrable) index vector.val

theorem joint_norm_bound (data : CuspidalRepresentation) (vector : data.smooth)
    (coefficient : BinaryFiniteGL → ℂ) (point : BinaryAdelicGL) (pair : BinaryFiniteGL × finiteCongruence) :
    ‖joint data vector coefficient point pair‖ ≤ ‖coefficient pair.1‖ * cuspSupNorm vector := by
  rw [joint, norm_mul]
  exact mul_le_mul_of_nonneg_left (realize_le_cuspSupNorm vector _) (norm_nonneg _)

theorem joint_integral_norm_bound (data : CuspidalRepresentation) (vector : data.smooth)
    (coefficient : BinaryFiniteGL → ℂ) (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure)
    (point : BinaryAdelicGL) :
    (∫ pair, ‖joint data vector coefficient point pair‖
      ∂BinaryProductHaar.finiteMeasure.prod FiniteCompactIntegral.measure) ≤
      (∫ binary, ‖coefficient binary‖ ∂BinaryProductHaar.finiteMeasure) * cuspSupNorm vector := by
  have bound := integral_mono_ae (joint_integrable data vector coefficient integrable point).norm
    ((integrable.norm.mul_const (cuspSupNorm vector)).comp_fst FiniteCompactIntegral.measure)
    (Filter.Eventually.of_forall (joint_norm_bound data vector coefficient point))
  rw [integral_fun_fst (ν := FiniteCompactIntegral.measure)
    (fun binary : BinaryFiniteGL => ‖coefficient binary‖ * cuspSupNorm vector)] at bound
  simpa only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul, integral_mul_const] using bound

theorem joint_modes_hasSum (data : CuspidalRepresentation) (vector : data.smooth)
    (coefficient : BinaryFiniteGL → ℂ) (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure)
    (point : BinaryAdelicGL) :
    HasSum (fun index : ℤ => ∫ pair, joint data (smoothMode data index vector) coefficient point pair
      ∂BinaryProductHaar.finiteMeasure.prod FiniteCompactIntegral.measure)
      (∫ pair, joint data vector coefficient point pair
        ∂BinaryProductHaar.finiteMeasure.prod FiniteCompactIntegral.measure) := by
  have summable : Summable (fun index : ℤ => ∫ pair, ‖joint data (smoothMode data index vector) coefficient point pair‖
      ∂BinaryProductHaar.finiteMeasure.prod FiniteCompactIntegral.measure) := by
    apply ((summable_cuspSupNorm_modes data vector).mul_left
      (∫ binary, ‖coefficient binary‖ ∂BinaryProductHaar.finiteMeasure)).of_nonneg_of_le
    · intro index
      exact integral_nonneg (fun _ => norm_nonneg _)
    · intro index
      exact joint_integral_norm_bound data _ coefficient integrable point
  have result := hasSum_integral_of_summable_integral_norm
    (fun index : ℤ => joint_integrable data (smoothMode data index vector) coefficient integrable point) summable
  have equality (pair : BinaryFiniteGL × finiteCongruence) :
      (∑' index : ℤ, joint data (smoothMode data index vector) coefficient point pair) =
        joint data vector coefficient point pair :=
    ((scalar_modes_hasSum data vector (point * atFinite pair.2.val * atFinite pair.1)).mul_left (coefficient pair.1)).tsum_eq
  simpa only [equality] using result

theorem realize_smoothMap {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (coefficient : BinaryFiniteGL → ℂ) (integrable : Integrable coefficient BinaryProductHaar.finiteMeasure)
    (point : BinaryAdelicGL) :
    data.cusp.realize (smoothMap data.cusp finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact
      coefficient integrable vector) point =
        ∫ pair, joint data.cusp vector coefficient point pair
          ∂BinaryProductHaar.finiteMeasure.prod FiniteCompactIntegral.measure := by
  have series := scalar_modes_hasSum data.cusp
    (smoothMap data.cusp finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact coefficient integrable vector) point
  have term (index : ℤ) :
      data.cusp.realize (smoothMode data.cusp index
        (smoothMap data.cusp finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact coefficient integrable vector)) point =
          ∫ pair, joint data.cusp (smoothMode data.cusp index vector) coefficient point pair
            ∂BinaryProductHaar.finiteMeasure.prod FiniteCompactIntegral.measure := by
    rw [smoothMap_modeProjection]
    let mode : fixedMode data.cusp finiteCongruence index :=
      ⟨smoothMode data.cusp index vector, smoothMode_mem_fixedMode data.cusp finiteCongruence
        finiteCongruence_isOpen finiteCongruence_isCompact index ⟨vector, fixed⟩⟩
    change data.cusp.realize (modeMap data.cusp finiteCongruence finiteCongruence_isOpen finiteCongruence_isCompact
      coefficient integrable index mode).val point = _
    rw [ProjectedCoefficientIntegral.realize_modeMap]
    exact (integral_prod_symm _ (joint_integrable data.cusp mode.val coefficient integrable point)).symm
  simp_rw [term] at series
  exact series.unique (joint_modes_hasSum data.cusp vector coefficient integrable point)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SmoothCoefficientIntegral
