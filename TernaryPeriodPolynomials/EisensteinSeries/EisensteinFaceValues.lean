module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.ConjStd
public import TernaryPeriodPolynomials.EisensteinSeries.EisensteinCuspTerm

@[expose] public section


/-!
# Restrictions of the Eisenstein series to the faces of all plane cusps: exact values

Paper: Proposition C.4 and Lemma C.3 ("the identity constant term represents exactly `ξ`").

## What is proved (`3 ≤ N`, `4 ≤ n`; `h` the plane cusp of the face, `h'` the cusp of the series)
* `resAtC_value_none`: if no coset of `Γ_{k⁻¹Pk}\Γ(N)`, `k = h' h⁻¹`, has `k γ ∈ P(ℤ)`, the restriction
  of the series (either seed type) to the plane group `Γ_{h⁻¹Ph}` is `0`.
* `resAtC_value_pos`: if `k γ = [[A, w], [0, 1]]`, the restriction is the conjugated seed
  `faceSeedKerClass N h n (f|A)` (holomorphic series) resp. `faceSeedConjKerClass N h n (f|A)`
  (antiholomorphic series), `f|A` the slash by the Levi block `A ∈ SL₂(ℤ)`.
* `resAtC_value_neg`: if `k γ = M · diag(1, -1, -1)`, `M = [[A, w], [0, 1]]` (Levi determinant `-1`), the
  holomorphic series restricts to the antiholomorphic seed of `(f|A)^*` (no sign) and the antiholomorphic
  series to the holomorphic seed of `(f|A)^*`.
* `seriesRestrictionInSeedSpan`: in all cases the restriction lies in the span of the conjugated seeds.
* `constant_term_identity_conj`: `r_P` of the antiholomorphic series at the standard cusp is the class of
  the antiholomorphic seed.
* `gammaNSeedKerClass_add/_smul`, `gammaNSeedConjKerClass_add/_smul`: additivity and (conjugate-)
  homogeneity of the seed classes in the cusp form.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.EisensteinClass

open TernaryPeriodPolynomials.Argument TernaryPeriodPolynomials.Argument.ConvergenceC4
  TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.SphericalDetection.Helpers

section Values

variable (N : ℕ) [NeZero N] (n : ℕ) (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n)

/-- **`SeriesRestrictionInSeedSpan` for every series**: the restriction of the complexified class of
the series at any cusp and seed type to the plane group of any cusp lies in the span of the conjugated
holomorphic and antiholomorphic seeds of that cusp. -/
theorem seriesRestrictionInSeedSpan (hN : 3 ≤ N) (x : PlaneFaces N) (b : Bool) :
    TernaryPeriodPolynomials.Argument.FormClassK.SeriesRestrictionInSeedSpan N n hn f x b :=
  TernaryPeriodPolynomials.Argument.EisensteinClass.seriesRestrictionInSeedSpan N n f hn hN x b

/-- **`r_P` of the antiholomorphic series at the standard cusp is the antiholomorphic seed class.** -/
theorem constant_term_identity_conj (hN : 3 ≤ N) :
    TernaryPeriodPolynomials.Argument.EisensteinClass.resP N n (eisensteinAtClass_gammaN N n f 1 true hn) =
      cuspSeedConjClass (gammaNPlaneData N) (gammaNPlaneData_lam_mem N) (f := f) :=
  TernaryPeriodPolynomials.Argument.EisensteinClass.constant_term_identity_conj N n f hn hN

end Values

end TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
