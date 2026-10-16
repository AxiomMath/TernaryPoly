module

public import TernaryPeriodPolynomials.Topology.Rational.Local.GeneratorDescent
public import TernaryPeriodPolynomials.SymmetricSpace.LocalOrientationPositive
public import TernaryPeriodPolynomials.SymmetricSpace.Covering

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceQuotientOrientation
open CategoryTheory HomologicalComplex RationalLocalMap RationalLocalChartHomology
open SymmetricSpacePositive SymmetricSpaceCovering SymmetricSpaceArithmeticProper

/-- The actual quotient covering as a continuous map. -/
def projection : C(Space,OrbitSpace) :=
  ⟨quotientProjection,quotientProjection_covering.continuous⟩

theorem projection_localHomeomorph : IsLocalHomeomorph projection :=
  quotientProjection_covering.isLocalHomeomorph

/-- Every principal-six deck map preserves the actual covering projection. -/
theorem projection_deck (g : DeckGroup) :
    projection.comp ⟨actionHomeomorph (realIntegral (deckInclusion g)),
      (actionHomeomorph (realIntegral (deckInclusion g))).continuous⟩ = projection := by
  ext S
  change quotientProjection (g • S) = quotientProjection S
  exact MulAction.orbitRel.Quotient.quotient_smul_eq

/-- Pushing the actual local generator through the covering is invariant under every deck map. -/
theorem pushedGenerator_deck (g : DeckGroup) (S : Space) :
    totalLocalMap projection projection_localHomeomorph 5
      ⟨g • S,SymmetricSpaceLocalOrientation.localGenerator (g • S)⟩ =
    totalLocalMap projection projection_localHomeomorph 5
      ⟨S,SymmetricSpaceLocalOrientation.localGenerator S⟩ := by
  apply totalLocalMap_deck projection projection_localHomeomorph
    (actionHomeomorph (realIntegral (deckInclusion g))) (projection_deck g) 5
    SymmetricSpaceLocalOrientation.localGenerator
  intro T
  exact SymmetricSpaceLocalOrientation.all_actionLocalMap_generator (realIntegral (deckInclusion g)) T

/-- The actual pushed generator is independent of every choice of a lifted point. -/
theorem pushedGenerator_fiber (S T : Space) (h : projection S = projection T) :
    totalLocalMap projection projection_localHomeomorph 5
      ⟨S,SymmetricSpaceLocalOrientation.localGenerator S⟩ =
    totalLocalMap projection projection_localHomeomorph 5
      ⟨T,SymmetricSpaceLocalOrientation.localGenerator T⟩ := by
  obtain ⟨g,hg⟩ := Quotient.exact h
  rw [← hg]
  exact pushedGenerator_deck g T

/-- The quotient point generator is an actual local class descended from the covering. -/
def localGenerator (y : OrbitSpace) : (localChains y).homology 5 :=
  descendedGenerator projection projection_localHomeomorph quotientProjection_surjective 5
    SymmetricSpaceLocalOrientation.localGenerator y

/-- Every lift gives exactly this quotient generator through the actual local covering map. -/
theorem localGenerator_projection (S : Space) :
    localHomeomorphMap projection projection_localHomeomorph S 5
      (SymmetricSpaceLocalOrientation.localGenerator S) = localGenerator (projection S) :=
  descendedGenerator_apply projection projection_localHomeomorph quotientProjection_surjective 5
    SymmetricSpaceLocalOrientation.localGenerator pushedGenerator_fiber S

/-- The descended actual quotient local generator is nonzero at every point. -/
theorem localGenerator_ne_zero (y : OrbitSpace) : localGenerator y ≠ 0 :=
  descendedGenerator_ne_zero projection projection_localHomeomorph quotientProjection_surjective 5
    SymmetricSpaceLocalOrientation.localGenerator pushedGenerator_fiber
    SymmetricSpaceLocalOrientation.localGenerator_ne_zero y

end TernaryPoly.SymmetricSpaceQuotientOrientation
