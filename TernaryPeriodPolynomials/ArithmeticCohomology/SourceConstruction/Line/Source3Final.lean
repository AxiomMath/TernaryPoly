module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.Source3Induced

@[expose] public section


/-!
# The level-three line source cocycle

The two analytic inputs of `LineSource3Induced` hold exactly as for the spherical line source
(`radicalAnalyticLine`, `coefficientAnalytic`).  Hence, for every level-three sign-twisted analytic
Levi cocycle `E` and every `χ` trivial on the integral units, `lineSource3 D E` is a source cocycle
for the line.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SourceConstruction

/-- **The level-three line source cocycle.** For `χ` trivial on the integral units and a
level-three sign-twisted analytic Levi cocycle `E`, `lineSource3 D E` is a smooth homogeneous
two-cocycle with line-induced coefficients (finite part supported on the identity cell). -/
theorem lineSource3_isSourceCocycle {n : ℕ} (D : InducingData n)
    (E : LineLeviCocycleData3 D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1) :
    IsSourceCocycle D .line (lineSource3 D E) :=
  lineSource3_isSourceCocycle_of_analytic D E hχ (radicalAnalyticLine n D.chi)
    (coefficientAnalytic D.chi hχ)

end TernaryPeriodPolynomials.SourceConstruction

end
