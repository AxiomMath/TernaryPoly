module

public import TernaryPeriodPolynomials.ArithmeticCohomology.PeriodLink.Cond
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Injective.Main

@[expose] public section


/-!
# Level-three period nonvanishing, unconditionally

Formalized by Claude Sonnet 5.5 (AxiomCode).

Combines `levelThreePeriodNonvanishing_of_injective` with the Eichler–Shimura injectivity for
`Γ₁'(3)` at the good-plane twist `det⁻¹`
(`LevelThreeInjective.Main.levelPeriodMap_injective_goodPlane`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.PeriodLink

/-- **Level-three period nonvanishing in every degree `n`**: the Eichler cocycle of a nonzero
holomorphic level-three vector of weight `n + 3` is not a crossed coboundary on `Γ₁'(3)`. -/
theorem levelThreePeriodNonvanishing (n : ℕ) :
    LevelThreeSource.LevelThreePeriodNonvanishing n :=
  levelThreePeriodNonvanishing_of_injective n
    (LevelThreeInjective.Main.levelPeriodMap_injective_goodPlane n)

end TernaryPeriodPolynomials.PeriodLink

end
