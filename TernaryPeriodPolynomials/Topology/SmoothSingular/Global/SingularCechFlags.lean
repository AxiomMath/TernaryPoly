module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularSubdomainSimplex
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechFlagCochains
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SingularCechBicomplex

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Set FreeActionLinearization SphereOddDegree
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open scoped Simplicial

variable {ι : Type} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i))
  (hcover : Set.univ ⊆ ⋃ i, U i)

/-- The actual flags of cover members containing an actual global small singular simplex. -/
abbrev SingularCoverFlag (n k : ℕ) := (smallSimplexIndexCover U hU hcover n).Flag k

/-- An actual simplex of a nonempty Čech intersection supplies its literal global small-simplex flag. -/
def localSimplexFlag (n k : ℕ) (t : Fin (k+1) → ι)
    (σ : SingularSimplex (TopCat.of (CoverOpen (cechDomain U t))) n) : SingularCoverFlag U hU hcover n (k+1) where
  labels := t
  point := ⟨globalizeSimplex (cechDomain U t) n σ,
    (coveringSimplex_small_iff U hU Set.univ hcover _).mpr
      ⟨t 0,fun r => mem_iInter.mp (mvSimplexMap σ r).property.2 0⟩⟩
  membership a r := mem_iInter.mp (mvSimplexMap σ r).property.2 a

/-- The actual global simplex in a flag restricts to the specified genuine quotient intersection. -/
def flagSimplex (n k : ℕ) (x : SingularCoverFlag U hU hcover n (k+1)) :
    SingularSimplex (TopCat.of (CoverOpen (cechDomain U x.labels))) n :=
  restrictGlobalSimplex (cechDomain U x.labels) n x.point.val
    (fun r => mem_iInter.mpr (fun a => x.membership a r))

/-- Local simplex to flag to local simplex is the identity on the actual singular simplex. -/
theorem flagSimplex_local (n k : ℕ) (t : Fin (k+1) → ι)
    (σ : SingularSimplex (TopCat.of (CoverOpen (cechDomain U t))) n) :
    flagSimplex U hU hcover n k (localSimplexFlag U hU hcover n k t σ) = σ :=
  restrict_globalizeSimplex (cechDomain U t) n σ

/-- Flag to local simplex to flag is the identity on the actual global small-simplex flag. -/
theorem localSimplexFlag_flag (n k : ℕ) (x : SingularCoverFlag U hU hcover n (k+1)) :
    localSimplexFlag U hU hcover n k x.labels (flagSimplex U hU hcover n k x) = x := by
  apply InvariantSetCover.Flag.ext
  · rfl
  · apply Subtype.ext
    exact globalize_restrictSimplex (cechDomain U x.labels) n x.point.val _

/-- The literal local simplex-to-flag map respects the actual deck action. -/
theorem localSimplexFlag_smul (n k : ℕ) (t : Fin (k+1) → ι) (g : DeckGroup)
    (σ : SingularSimplex (TopCat.of (CoverOpen (cechDomain U t))) n) :
    localSimplexFlag U hU hcover n k t (g • σ) = g • localSimplexFlag U hU hcover n k t σ := by
  apply InvariantSetCover.Flag.ext
  · rfl
  · apply Subtype.ext
    exact globalizeSimplex_smul (cechDomain U t) n g σ

/-- The literal flag-to-local-simplex map respects the actual deck action. -/
theorem flagSimplex_smul (n k : ℕ) (g : DeckGroup) (x : SingularCoverFlag U hU hcover n (k+1)) :
    flagSimplex U hU hcover n k (g • x) = g • flagSimplex U hU hcover n k x :=
  restrictGlobalSimplex_smul (cechDomain U x.labels) n g x.point.val _ _

/-- Flag selection is the actual singular pushforward along the genuine inclusion of intersections. -/
theorem flagSimplex_select (n p q : ℕ) (f : Fin (p+1) → Fin (q+1))
    (x : SingularCoverFlag U hU hcover n (q+1)) :
    flagSimplex U hU hcover n p ((smallSimplexIndexCover U hU hcover n).select f x) =
      (TopCat.toSSet.map (coverInclusion (cechDomain_select_subset U f x.labels))).app (.op ⦋n⦌)
        (flagSimplex U hU hcover n q x) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (CoverOpen (cechDomain U (x.labels ∘ f)))) (.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro r
  apply Subtype.ext
  exact (restrictGlobalSimplex_value (cechDomain U (x.labels ∘ f)) n x.point.val
    (fun s => mem_iInter.mpr (fun a => x.membership (f a) s)) r).trans
    (restrictGlobalSimplex_value (cechDomain U x.labels) n x.point.val
      (fun s => mem_iInter.mpr (fun a => x.membership a s)) r).symm

end TernaryPoly.SmoothSingularGlobal
