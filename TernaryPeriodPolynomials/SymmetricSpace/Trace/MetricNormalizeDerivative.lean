module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricDerivative
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-! Differentiate the actual trace-normalization map with its radial correction. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceTraceMetric

open Matrix SymmetricSpacePositive
open scoped ContDiff Matrix.Norms.Elementwise

def traceCLM : Mat →L[ℝ] ℝ := (Matrix.traceLinearMap (Fin 3) ℝ ℝ).toContinuousLinearMap

@[simp] theorem traceCLM_apply (S : Mat) : traceCLM S = S.trace := rfl

def normalizationDerivative (S : Mat) : Mat →L[ℝ] Mat :=
  S.trace⁻¹ • ContinuousLinearMap.id ℝ Mat +
    (-(S.trace ^ 2)⁻¹ • traceCLM).smulRight S

theorem hasFDerivAt_normalize (S : Mat) (hS : S.trace ≠ 0) :
    HasFDerivAt normalize (normalizationDerivative S) S := by
  have hi := (hasDerivAt_inv hS).comp_hasFDerivAt S (traceCLM.hasFDerivAt)
  exact hi.smul (hasFDerivAt_id S)

/-- The actual derivative has the exact normalized tangent plus radial-correction form. -/
theorem normalizationDerivative_apply (S U : Mat) :
    normalizationDerivative S U =
      S.trace⁻¹ • (U + (-S.trace⁻¹ * U.trace) • S) := by
  simp [normalizationDerivative, smul_add, smul_smul]
  congr 1
  ring

end TernaryPoly.SymmetricSpaceTraceMetric
