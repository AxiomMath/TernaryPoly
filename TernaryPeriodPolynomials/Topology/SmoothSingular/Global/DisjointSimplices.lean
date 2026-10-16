module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.DisjointCover

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory FreeActionLinearization SphereOddDegree CoveringSingularOrbits
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open scoped Simplicial
namespace DisjointQuotientCover
variable {V : Set OrbitSpace} {ι : Type} (U : DisjointQuotientCover V ι)

/-- The actual inclusion of a component simplex into the whole covered open. -/
def includeSimplex (i : ι) (n : ℕ)
    (σ : SingularSimplex (TopCat.of (CoverOpen (U.domain i))) n) :
    SingularSimplex (TopCat.of (CoverOpen V)) n :=
  (TopCat.toSSet.map (coverInclusion (U.subset i))).app (.op ⦋n⦌) σ

/-- Literal component inclusion leaves every coordinate unchanged. -/
theorem includeSimplex_value (i : ι) (n : ℕ)
    (σ : SingularSimplex (TopCat.of (CoverOpen (U.domain i))) n)
    (t : Convexity.StdSimplex ℝ (Fin (n+1))) :
    (mvSimplexMap (U.includeSimplex i n σ) t).val = (mvSimplexMap σ t).val := rfl

/-- The label of an actual included component simplex is its original component. -/
theorem simplexIndex_include (i : ι) (n : ℕ)
    (σ : SingularSimplex (TopCat.of (CoverOpen (U.domain i))) n) :
    U.simplexIndex n (U.includeSimplex i n σ) = i :=
  U.lifted.index_eq_of_mem i (mvSimplexMap σ (vertex n)).property.2

/-- Restricting a simplex to its actual component and including it recovers the original. -/
theorem include_componentSimplex (n : ℕ) (σ : SingularSimplex (TopCat.of (CoverOpen V)) n) :
    U.includeSimplex (U.simplexIndex n σ) n (U.componentSimplex n σ) = σ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (CoverOpen V)) (.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  exact U.componentSimplex_value n σ t

/-- Codomain restriction of an included component simplex is literally that same simplex. -/
theorem restrictGlobal_include (i : ι) (n : ℕ)
    (σ : SingularSimplex (TopCat.of (CoverOpen (U.domain i))) n)
    (hσ : SimplexInDomain (U.domain i) (globalizeSimplex V n (U.includeSimplex i n σ))) :
    restrictGlobalSimplex (U.domain i) n (globalizeSimplex V n (U.includeSimplex i n σ)) hσ = σ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (CoverOpen (U.domain i))) (.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  exact restrictGlobalSimplex_value _ n _ _ t

/-- Actual restriction of a deck-translated simplex equals deck translation of its restriction,
with both containment proofs kept explicit to avoid dependent rewriting. -/
theorem restrict_globalize_smul (W : Set OrbitSpace) (n : ℕ) (g : DeckGroup)
    (σ : SingularSimplex (TopCat.of (CoverOpen V)) n)
    (hσ : SimplexInDomain W (globalizeSimplex V n σ))
    (hgσ : SimplexInDomain W (globalizeSimplex V n (g • σ))) :
    restrictGlobalSimplex W n (globalizeSimplex V n (g • σ)) hgσ =
      g • restrictGlobalSimplex W n (globalizeSimplex V n σ) hσ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (CoverOpen W)) (.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change (mvSimplexMap (restrictGlobalSimplex W n (globalizeSimplex V n (g • σ)) hgσ) t).val =
    (mvSimplexMap (g • restrictGlobalSimplex W n (globalizeSimplex V n σ) hσ) t).val
  rw [restrictGlobalSimplex_value,globalizeSimplex_value,simplexMap_smul,simplexMap_smul]
  exact congrArg (deckMap g) (restrictGlobalSimplex_value W n (globalizeSimplex V n σ) hσ t).symm

end DisjointQuotientCover
end TernaryPoly.SmoothSingularGlobal
