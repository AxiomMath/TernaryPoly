module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ScalarCompact
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Resolution
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Subdivision

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Set SymmetricSpaceCovering
variable (A : Rep.{0} ℚ DeckGroup)

/-- Actual real ordinary covering singular cohomology detects rational classes in every degree. -/
theorem globalSingular_real_detects_rational (n : ℕ) :
    Function.Injective (realSingularCohomologyInclusion DeckGroup (TopCat.of (CoverOpen univ)) A n) :=
  realSingularCohomology_injective DeckGroup (TopCat.of (CoverOpen univ)) A n

/-- The scalar-extension bridge preserves the literal compact-to-ordinary covering singular map. -/
theorem globalSingular_real_compact_square (n : ℕ) :
    rationalCoverCompactForget A n ≫ realSingularCohomologyInclusion DeckGroup (TopCat.of (CoverOpen univ)) A n =
      realCoverCompactInclusion A n ≫ forgetReal.map (realCoverCompactForget A n) :=
  realCoverCompact_forget_square A n

end TernaryPoly.SmoothSingularGlobal
