module

public import TernaryPeriodPolynomials.Analysis.Scalar.FriedrichsEnvelope
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

@[expose] public section


/-! The actual commutator envelope is continuous and compactly supported. -/
noncomputable section
namespace TernaryPoly.ScalarFriedrichsEnvelope
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuous_envelope (κ : E → ℝ) (v : E) (L A B : ℝ) (hκ : ContDiff ℝ 1 κ) :
    Continuous (envelope κ v L A B) := by
  exact (continuous_const.mul (continuous_norm.mul
    (((hκ.continuous_fderiv one_ne_zero).clm_apply continuous_const).norm))).add
    (continuous_const.mul hκ.continuous.norm)

theorem compact_envelope (κ : E → ℝ) (v : E) (L A B : ℝ) (hcκ : HasCompactSupport κ) :
    HasCompactSupport (envelope κ v L A B) :=
  ((hcκ.fderiv_apply ℝ v).norm.mul_left.mul_left).add (hcκ.norm.mul_left)

end TernaryPoly.ScalarFriedrichsEnvelope
