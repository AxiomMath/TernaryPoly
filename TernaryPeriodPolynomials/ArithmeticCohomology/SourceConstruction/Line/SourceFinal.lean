module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.SourceInduced
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceFinal

@[expose] public section


/-!
# The line source cocycle

The two analytic inputs of `LineSourceInduced` hold: the line radical is real analytic along the
Iwasawa factor and the matrix coefficients of the coefficient representation are real analytic (for a
character trivial on the real ideles).  Hence, for every sign-twisted analytic Levi cocycle `E` and
every `χ` trivial on the integral units, `lineSource D E` is a source cocycle for the line.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.SourceConstruction

theorem radicalAnalyticLine (n : ℕ) (χ : RankOneCharacter) : RadicalAnalyticLine n χ := by
  intro Q μ
  unfold Smooth
  have hmaps : Set.MapsTo (fun A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ => A 0)
      {A : Fin 1 → Matrix (Fin 3) (Fin 3) ℝ | ∀ i, (A i).det ≠ 0}
      {B : Matrix (Fin 3) (Fin 3) ℝ | B.det ≠ 0} := fun A hA => hA 0
  exact (lineRadical_iwasawaB_contDiffOn n χ Q μ).comp
    (contDiff_apply ℝ (Matrix (Fin 3) (Fin 3) ℝ) (0 : Fin 1)).contDiffOn hmaps

/-- **The line source cocycle.** For `χ` trivial on the integral units and a sign-twisted analytic
Levi cocycle `E`, `lineSource D E` is a smooth homogeneous two-cocycle with line-induced
coefficients. -/
theorem lineSource_isSourceCocycle {n : ℕ} (D : InducingData n)
    (E : LineLeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1) :
    IsSourceCocycle D .line (lineSource D E) :=
  lineSource_isSourceCocycle_of_analytic D E hχ (radicalAnalyticLine n D.chi)
    (coefficientAnalytic D.chi hχ)

end TernaryPeriodPolynomials.SourceConstruction

end
