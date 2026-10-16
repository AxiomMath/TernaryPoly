module

public import TernaryPeriodPolynomials.Analysis.ScaledScalarKernel
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

@[expose] public section


/-! Genuine smoothness and compact support of the mass-preserving scalar dilations. -/
noncomputable section
namespace TernaryPoly.ScaledScalarKernel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_dilate {n : ℕ∞} (κ : E → ℝ) (c : ℝ) (hκ : ContDiff ℝ n κ) :
    ContDiff ℝ n (dilate c κ) :=
  contDiff_const.mul (hκ.comp (contDiff_const.smul contDiff_id))

theorem compact_dilate (κ : E → ℝ) (c : ℝ) (hc : c ≠ 0) (hκ : HasCompactSupport κ) :
    HasCompactSupport (dilate c κ) := by
  have h := hκ.comp_homeomorph (Homeomorph.smul (isUnit_iff_ne_zero.mpr hc).unit)
  change HasCompactSupport (fun x => κ (c • x)) at h
  exact h.mul_left

theorem nonneg_dilate (κ : E → ℝ) (c : ℝ) (hc : 0 ≤ c) (hκ : ∀ x, 0 ≤ κ x) (x : E) :
    0 ≤ dilate c κ x := mul_nonneg (pow_nonneg hc _) (hκ _)

end TernaryPoly.ScaledScalarKernel
