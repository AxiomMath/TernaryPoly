module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.DisjointLabels
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularSubdomainSimplex

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory FreeActionLinearization SphereOddDegree CoveringSingularOrbits
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open scoped Simplicial

/-- A genuine disjoint open cover of a quotient subset, with literal inclusions and covering. -/
structure DisjointQuotientCover (V : Set OrbitSpace) (ι : Type) where
  domain : ι → Set OrbitSpace
  isOpen_domain : ∀ i, IsOpen (domain i)
  subset : ∀ i, domain i ⊆ V
  disjoint : Pairwise (fun i j => Disjoint (domain i) (domain j))
  covers : V ⊆ ⋃ i, domain i

namespace DisjointQuotientCover
variable {V : Set OrbitSpace} {ι : Type} (U : DisjointQuotientCover V ι)

/-- The actual inverse-image cover in the genuine coordinate covering. -/
def lifted : DisjointOpenCover (CoverOpen V) ι where
  domain i := {x | coordinateProjection x.val ∈ U.domain i}
  isOpen_domain i :=
    ((coordinateProjection_continuousOn.comp_continuous continuous_subtype_val
      (fun x : CoverOpen V => x.property.1))).isOpen_preimage _ (U.isOpen_domain i)
  disjoint := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hx hy
    exact (U.disjoint hij).le_bot ⟨hx,hy⟩
  covers x := by
    obtain ⟨i,hi⟩ := mem_iUnion.mp (U.covers x.property.2)
    exact ⟨i,hi⟩

/-- Actual component labels are invariant under the genuine deck action. -/
theorem label_smul (g : DeckGroup) (x : CoverOpen V) :
    U.lifted.label (g • x) = U.lifted.label x := by
  apply U.lifted.index_eq_of_mem
  change coordinateProjection (deckMap g x.val) ∈ U.domain (U.lifted.index x)
  rw [coordinateProjection_deck g x.property.1]
  exact U.lifted.index_mem x

/-- The actual component of an entire singular simplex, read at its first vertex. -/
def simplexIndex (n : ℕ) (σ : SingularSimplex (TopCat.of (CoverOpen V)) n) : ι :=
  U.lifted.label (mvSimplexMap σ (vertex n))

/-- Every actual point of a singular simplex lies in the same genuine component open. -/
theorem simplex_mem (n : ℕ) (σ : SingularSimplex (TopCat.of (CoverOpen V)) n)
    (t : Convexity.StdSimplex ℝ (Fin (n+1))) :
    coordinateProjection (mvSimplexMap σ t).val ∈ U.domain (U.simplexIndex n σ) := by
  have h := U.lifted.index_mem (mvSimplexMap σ t)
  have he := U.lifted.label_comp_eq (mvSimplexMap σ) t (vertex n)
  exact (congrArg (fun i => coordinateProjection (mvSimplexMap σ t).val ∈ U.domain i) he).mp h

/-- Actual deck translation preserves the component of a singular simplex. -/
theorem simplexIndex_smul (n : ℕ) (g : DeckGroup)
    (σ : SingularSimplex (TopCat.of (CoverOpen V)) n) :
    U.simplexIndex n (g • σ) = U.simplexIndex n σ := by
  unfold simplexIndex
  rw [simplexMap_smul]
  exact U.label_smul g _

/-- The actual globalized simplex satisfies the literal subdomain predicate for its component. -/
theorem simplexInDomain (n : ℕ) (σ : SingularSimplex (TopCat.of (CoverOpen V)) n) :
    SimplexInDomain (U.domain (U.simplexIndex n σ)) (globalizeSimplex V n σ) :=
  U.simplex_mem n σ

/-- Literal codomain restriction puts the entire actual simplex in its selected component. -/
def componentSimplex (n : ℕ) (σ : SingularSimplex (TopCat.of (CoverOpen V)) n) :
    SingularSimplex (TopCat.of (CoverOpen (U.domain (U.simplexIndex n σ)))) n :=
  restrictGlobalSimplex _ n (globalizeSimplex V n σ) (U.simplexInDomain n σ)

/-- Actual component restriction leaves all coordinates of the simplex unchanged. -/
theorem componentSimplex_value (n : ℕ) (σ : SingularSimplex (TopCat.of (CoverOpen V)) n)
    (t : Convexity.StdSimplex ℝ (Fin (n+1))) :
    (mvSimplexMap (U.componentSimplex n σ) t).val = (mvSimplexMap σ t).val :=
  restrictGlobalSimplex_value _ n (globalizeSimplex V n σ) _ t

end DisjointQuotientCover
end TernaryPoly.SmoothSingularGlobal
