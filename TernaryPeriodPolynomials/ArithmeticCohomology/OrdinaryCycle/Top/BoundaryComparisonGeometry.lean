module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonRelative
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.IncidenceHomologyComplete
public import TernaryPeriodPolynomials.SymmetricSpace.Bordified.Contractible

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryTopBoundaryComparison
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence
open EquivariantSingularResolution SingularCoverNaturality SingularBoundaryRestriction
open SymmetricSpaceRationalGluing SymmetricSpaceBoundaryIncidenceHomology

/-- The actual equivariant singular inclusion of the whole upstairs boundary. -/
abbrev upstairsBoundaryChainMap : boundaryChains ⟶ equivariantChains principalSix (TopCat.of Glued) :=
  chainMap boundaryInclusion boundaryInclusion_equivariant

/-- Actual relative representation chains of the entire bordification pair. -/
abbrev upstairsRelativeChains := cokernel upstairsBoundaryChainMap

/-- The literal boundary/absolute/relative short exact sequence. -/
abbrev upstairsRelativeSequence := relativeSequence boundaryInclusion boundaryInclusion_equivariant

/-- The actual inclusion gives a genuine short exact sequence, not an assumed geometric model. -/
theorem upstairsRelativeSequence_shortExact : upstairsRelativeSequence.ShortExact :=
  relativeSequence_shortExact boundaryInclusion boundaryInclusion_equivariant boundaryInclusion_injective

/-- Positive-degree homology of the actual upstairs bordification vanishes equivariantly. -/
theorem upstairsAbsoluteHomology_isZero (n : ℕ) (hn : n ≠ 0) :
    IsZero ((equivariantChains principalSix (TopCat.of Glued)).homology n) :=
  (equivariantChains_exactAt principalSix (TopCat.of Glued) n hn).isZero_homology

/-- The genuine relative connecting morphism identifies H2 of the pair with boundary H1. -/
def upstairsRelativeH2BoundaryIso : upstairsRelativeChains.homology 2 ≅ boundaryChains.homology 1 :=
  upstairsRelativeSequence_shortExact.δIso 2 1 rfl
    (upstairsAbsoluteHomology_isZero 2 (by decide))
    (upstairsAbsoluteHomology_isZero 1 (by decide))

/-- The actual H2-to-H1 comparison is the literal long-exact-sequence connecting morphism. -/
theorem upstairsRelativeH2BoundaryIso_hom :
    upstairsRelativeH2BoundaryIso.hom = upstairsRelativeSequence_shortExact.δ 2 1 rfl := rfl

/-- The genuine relative homology is identified with ordinary incidence cycles using the
actual connecting morphism and the actual boundary MV comparison. -/
def upstairsRelativeH2OrdinaryIso : upstairsRelativeChains.homology 2 ≅ ordinaryCyclesRep :=
  upstairsRelativeH2BoundaryIso ≪≫ boundaryH1OrdinaryCyclesIso

/-- The relative-to-ordinary comparison retains the literal MV edge coefficients and sign. -/
theorem upstairsRelativeH2OrdinaryIso_edge :
    upstairsRelativeH2OrdinaryIso.hom ≫ ordinaryCycleInclusion =
      upstairsRelativeSequence_shortExact.δ 2 1 rfl ≫ boundaryEdgeMap := by
  change (upstairsRelativeH2BoundaryIso.hom ≫ boundaryH1OrdinaryCyclesIso.hom) ≫ _ = _
  rw [Category.assoc, boundaryH1OrdinaryCyclesIso_edge, upstairsRelativeH2BoundaryIso_hom]
  rfl

/-- Actual relative chain groups are projective under the proved free principal-six action. -/
theorem upstairsRelativeDegree_projective (n : ℕ) : Projective (upstairsRelativeChains.X n) := by
  let : IsCancelSMul principalSix Glued := wholeQuotientCovering.isCancelSMul
  exact relativeDegree_projective boundaryInclusion boundaryInclusion_equivariant boundaryInclusion_injective n

end TernaryPoly.OrdinaryTopBoundaryComparison
