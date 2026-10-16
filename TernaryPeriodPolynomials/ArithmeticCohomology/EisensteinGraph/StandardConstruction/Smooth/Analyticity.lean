module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Smooth.Jets

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SmoothAnalyticity

/-- The statement's literal regularity order is the analytic order of the pinned library. -/
theorem smooth_iff_analyticOn {size arity : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : (Fin arity → GeneralLinearGroup (Fin size) ℝ) → E) :
    Smooth function ↔ AnalyticOn ℝ (SmoothJets.matrixExtension function) (SmoothJets.domain size arity) :=
  contDiffOn_omega_iff_analyticOn (SmoothJets.domain_open size arity).uniqueDiffOn

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SmoothAnalyticity
