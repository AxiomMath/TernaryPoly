module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ClassIdentity

@[expose] public section


/-!
# Lemma C.3 (`ar:lem:seed`): the seed classes are the restricted cuspidal plane summand

At the bad plane, level one, odd `n = 2k + 1`: for every level-one cusp form `f` of weight
`n + 3`, the element `b` of the automorphic plane span realizing `per f` (vanishing at the good
plane) restricts on `Λ₀⁺ = ℤ² ⋊ SL₂(ℤ)` to `(n+1)/2` times the complexified de Rham class of
the reflection-invariant combination `ω_f + \overline{ω_{f^*}}` of the holomorphic and
antiholomorphic seeds. With the injectivity of the period map this identifies the restriction of
the cuspidal plane classes with the span of the seed classes.

Written by Claude Opus 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.Argument.Statements.SeedClassIdentity

open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Spectral.CuspReduction

/-- **Lemma C.3, S4c (bad plane, level one).** -/
theorem lemma_C_3_seed_class_levelOne (k : ℕ) (f : CuspForm Lvl1 (((2 * k + 1) + 3 : ℕ) : ℤ)) :
    ∃ b ∈ automorphicPlaneSpan (2 * k + 1),
      cuspRes (2 * k + 1) trivialCharacter .plane true b = 0 ∧
      plusResH2 (2 * k + 1) (ambientToGroupH2 (2 * k + 1)
          (cuspRes (2 * k + 1) trivialCharacter .plane false b)) =
        ((((2 * k + 1 : ℕ) : ℂ) + 1) / 2) • complexify (2 * k + 1)
          (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty plusPlaneData.action
            (plusPlaneData.rhoR (2 * k + 1)) (reflSeedInv plusPlaneData plus_hΛ f 1)) :=
  seed_class_identity k f

end TernaryPeriodPolynomials.Argument.Statements.SeedClassIdentity
