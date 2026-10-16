module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.RotationCompleteness

@[expose] public section


open MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

variable {X E F : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
  [CompactSpace X] [T2Space X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_multilinear_integrable (measure : Measure X) [IsFiniteMeasure measure] {order : ℕ}
    (family : X → ContinuousMultilinearMap ℝ (fun _ : Fin order => E) F)
    (continuous : ∀ vectors, Continuous (fun point => family point vectors))
    (vectors : Fin order → E) : Integrable (fun point => family point vectors) measure := by
  apply integrableOn_univ.mp
  exact ContinuousOn.integrableOn_compact isCompact_univ (continuous vectors).continuousOn

noncomputable def compactMultilinearIntegralMap (measure : Measure X) [IsFiniteMeasure measure] {order : ℕ}
    (family : X → ContinuousMultilinearMap ℝ (fun _ : Fin order => E) F)
    (continuous : ∀ vectors, Continuous (fun point => family point vectors)) :
    MultilinearMap ℝ (fun _ : Fin order => E) F where
  toFun vectors := ∫ point, family point vectors ∂measure
  map_update_add' vectors index first second := by
    simp only [ContinuousMultilinearMap.map_update_add]
    exact integral_add (compact_multilinear_integrable measure family continuous _)
      (compact_multilinear_integrable measure family continuous _)
  map_update_smul' vectors index scalar vector := by
    simp only [ContinuousMultilinearMap.map_update_smul]
    exact integral_smul scalar _

theorem compactMultilinearIntegralMap_bound (measure : Measure X) [IsProbabilityMeasure measure] {order : ℕ}
    (family : X → ContinuousMultilinearMap ℝ (fun _ : Fin order => E) F)
    (continuous : ∀ vectors, Continuous (fun point => family point vectors))
    (bound : ℝ) (bounded : ∀ point, ‖family point‖ ≤ bound) (vectors : Fin order → E) :
    ‖compactMultilinearIntegralMap measure family continuous vectors‖ ≤ bound * ∏ index, ‖vectors index‖ := by
  calc
    _ ≤ ∫ point, ‖family point vectors‖ ∂measure := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : X, bound * ∏ index, ‖vectors index‖ ∂measure := by
      apply integral_mono (compact_multilinear_integrable measure family continuous vectors).norm (integrable_const _)
      intro point
      exact (family point).le_opNorm vectors |>.trans
        (mul_le_mul_of_nonneg_right (bounded point) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
    _ = _ := by simp

noncomputable def compactMultilinearIntegral (measure : Measure X) [IsProbabilityMeasure measure] {order : ℕ}
    (family : X → ContinuousMultilinearMap ℝ (fun _ : Fin order => E) F)
    (continuous : ∀ vectors, Continuous (fun point => family point vectors))
    (bound : ℝ) (bounded : ∀ point, ‖family point‖ ≤ bound) :
    ContinuousMultilinearMap ℝ (fun _ : Fin order => E) F :=
  (compactMultilinearIntegralMap measure family continuous).mkContinuous bound
    (compactMultilinearIntegralMap_bound measure family continuous bound bounded)

theorem compactMultilinearIntegral_apply (measure : Measure X) [IsProbabilityMeasure measure] {order : ℕ}
    (family : X → ContinuousMultilinearMap ℝ (fun _ : Fin order => E) F)
    (continuous : ∀ vectors, Continuous (fun point => family point vectors))
    (bound : ℝ) (bounded : ∀ point, ‖family point‖ ≤ bound) (vectors : Fin order → E) :
    compactMultilinearIntegral measure family continuous bound bounded vectors =
      ∫ point, family point vectors ∂measure := rfl

theorem compactMultilinearIntegral_norm_le (measure : Measure X) [IsProbabilityMeasure measure] {order : ℕ}
    (family : X → ContinuousMultilinearMap ℝ (fun _ : Fin order => E) F)
    (continuous : ∀ vectors, Continuous (fun point => family point vectors))
    (bound : ℝ) (bound_nonnegative : 0 ≤ bound) (bounded : ∀ point, ‖family point‖ ≤ bound) :
    ‖compactMultilinearIntegral measure family continuous bound bounded‖ ≤ bound :=
  MultilinearMap.mkContinuous_norm_le _ bound_nonnegative _

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
