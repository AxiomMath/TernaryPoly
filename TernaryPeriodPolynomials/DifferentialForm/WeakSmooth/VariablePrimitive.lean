module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Fiber.Integral
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Test.Primitive

@[expose] public section


/-! Smoothness of the actual test antiderivative with variable upper endpoint. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory
open scoped ContDiff
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The genuine last-coordinate antiderivative from zero. -/
def fiberTestPrimitiveRaw (f : E × ℝ → ℝ) (p : E × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..p.2, f (p.1, t)

/-- The interval-integral antiderivative is jointly smooth, including at upper endpoint zero. -/
theorem fiberTestPrimitiveRaw_contDiff {f : E × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fiberTestPrimitiveRaw f) := by
  have hg : ContDiff ℝ ∞ (fun p : (E × ℝ) × ℝ => f (p.1.1, p.1.2 * p.2)) :=
    hf.comp ((contDiff_fst.fst).prodMk ((contDiff_fst.snd).mul contDiff_snd))
  have hh := contDiff_snd.mul (fiberTestIntegralRaw_contDiff hg)
  have he : (fun p : E × ℝ => p.2 *
      fiberTestIntegralRaw (fun q : (E × ℝ) × ℝ => f (q.1.1, q.1.2 * q.2)) p) =
      fiberTestPrimitiveRaw f := by
    funext p
    simpa only [fiberTestIntegralRaw, fiberTestPrimitiveRaw, smul_eq_mul, mul_zero, mul_one] using
      (intervalIntegral.smul_integral_comp_mul_left (fun t => f (p.1, t)) p.2
        (a := (0 : ℝ)) (b := 1))
  exact he ▸ hh

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The last-coordinate derivative is the literal input function. -/
theorem fiberTestPrimitiveRaw_hasDerivAt {f : E × ℝ → ℝ} (hf : Continuous f)
    (x : E) (t : ℝ) :
    HasDerivAt (fun s => fiberTestPrimitiveRaw f (x, s)) (f (x, t)) t :=
  ((hf.comp (continuous_const.prodMk continuous_id)).integral_hasStrictDerivAt 0 t).hasDerivAt

end TernaryPoly.PolynomialFormWeakSmooth
