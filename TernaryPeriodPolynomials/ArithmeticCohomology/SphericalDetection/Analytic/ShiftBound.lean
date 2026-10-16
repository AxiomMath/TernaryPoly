module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Analytic.SeriesIntegral

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def shiftedSeriesBound {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (series : FormalMultilinearSeries ℝ E F) (radius : NNReal) (index : ℕ) : NNReal :=
  ∑' (term : (degree : ℕ) × {chosen : Finset (Fin (index + degree)) // chosen.card = degree}),
    ‖series (index + term.1)‖₊ * radius ^ term.1

theorem shiftedSeriesBound_summable {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (series : FormalMultilinearSeries ℝ E F) (shiftRadius radius : NNReal)
    (inside : (shiftRadius : ENNReal) + radius < series.radius) :
    Summable (fun index => shiftedSeriesBound series shiftRadius index * radius ^ index) := by
  have total := series.changeOriginSeries_summable_aux₁ inside
  have outer := (NNReal.summable_sigma.mp total).2
  simpa only [shiftedSeriesBound, NNReal.tsum_mul_right] using outer

theorem shiftedSeriesBound_terms_summable {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (series : FormalMultilinearSeries ℝ E F) (shiftRadius radius : NNReal)
    (positive : 0 < radius) (inside : (shiftRadius : ENNReal) + radius < series.radius) (index : ℕ) :
    Summable (fun term : (degree : ℕ) × {chosen : Finset (Fin (index + degree)) // chosen.card = degree} =>
      ‖series (index + term.1)‖₊ * shiftRadius ^ term.1) := by
  have inner := (NNReal.summable_sigma.mp (series.changeOriginSeries_summable_aux₁ inside)).1 index
  have rescaled := inner.mul_right (radius ^ index)⁻¹
  simpa only [mul_assoc, mul_inv_cancel₀ (pow_ne_zero index (ne_of_gt positive)), mul_one] using rescaled

theorem nnnorm_changeOrigin_le_shiftedSeriesBound {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (series : FormalMultilinearSeries ℝ E F) (shiftRadius radius : NNReal)
    (positive : 0 < radius) (inside : (shiftRadius : ENNReal) + radius < series.radius)
    (point : E) (point_bound : ‖point‖₊ ≤ shiftRadius) (index : ℕ) :
    ‖series.changeOrigin point index‖₊ ≤ shiftedSeriesBound series shiftRadius index := by
  have point_inside : (‖point‖₊ : ENNReal) < series.radius :=
    lt_of_le_of_lt (by exact_mod_cast point_bound) (lt_of_le_of_lt le_self_add inside)
  have summable := shiftedSeriesBound_terms_summable series shiftRadius radius positive inside index
  have dominated (term : (degree : ℕ) × {chosen : Finset (Fin (index + degree)) // chosen.card = degree}) :
      ‖series (index + term.1)‖₊ * ‖point‖₊ ^ term.1 ≤
        ‖series (index + term.1)‖₊ * shiftRadius ^ term.1 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) point_bound term.1) (by positivity)
  exact (series.nnnorm_changeOrigin_le index point_inside).trans
    ((NNReal.summable_of_le dominated summable).tsum_le_tsum dominated summable)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
