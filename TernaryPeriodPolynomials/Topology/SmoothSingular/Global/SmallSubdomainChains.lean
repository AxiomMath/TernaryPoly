module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.LocalSmallChains

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory FreeActionLinearization SphereOddDegree
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open SphereOddDegree.AffineBarycentricSubdivision
open scoped Simplicial

variable {ι : Type} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i))
  {V W : Set OrbitSpace} (hV : V ⊆ ⋃ i, U i) (hW : W ⊆ ⋃ i, U i) (hVW : V ⊆ W)

/-- Literal pushforward of a simplex along an actual covering-subdomain inclusion. -/
def includeSubdomainSimplex (n : ℕ) (σ : SingularSimplex (TopCat.of (CoverOpen V)) n) :
    SingularSimplex (TopCat.of (CoverOpen W)) n :=
  (TopCat.toSSet.map (coverInclusion hVW)).app (.op ⦋n⦌) σ

/-- Genuine cover-smallness is preserved by literal inclusion of covering subdomains. -/
theorem includeSubdomainSimplex_small (n : ℕ) (σ : SingularSimplex (TopCat.of (CoverOpen V)) n)
    (hσ : IsSmallSimplex (liftedOpenCover U hU V hV) σ) :
    IsSmallSimplex (liftedOpenCover U hU W hW) (includeSubdomainSimplex hVW n σ) := by
  obtain ⟨i,hi⟩ := (coveringSimplex_small_iff U hU V hV σ).mp hσ
  apply (coveringSimplex_small_iff U hU W hW _).mpr
  exact ⟨i,hi⟩

/-- The actual subdomain chain map preserves the actual small-simplex span. -/
theorem smallSubdomain_span (n : ℕ) (c : (underlyingChains (TopCat.of (CoverOpen V))).X n)
    (hc : c ∈ predicateSpan (TopCat.of (CoverOpen V)) n
      (IsSmallSimplex (liftedOpenCover U hU V hV))) :
    (SmoothSingularComparison.realSingularChainMap (coverInclusion hVW)).f n c ∈
      predicateSpan (TopCat.of (CoverOpen W)) n (IsSmallSimplex (liftedOpenCover U hU W hW)) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨σ,hσ,rfl⟩ := hc
    have he : (SmoothSingularComparison.realSingularChainMap (coverInclusion hVW)).f n
        (chainGenerator ℝ (TopCat.of (CoverOpen V)) n σ) =
        chainGenerator ℝ (TopCat.of (CoverOpen W)) n (includeSubdomainSimplex hVW n σ) :=
      congrArg (fun f => f.hom 1) (singularGenerator_map (coverInclusion hVW) n σ)
    exact he.symm ▸ Submodule.subset_span
      ⟨includeSubdomainSimplex hVW n σ,includeSubdomainSimplex_small U hU hV hW hVW n σ hσ,rfl⟩
  | zero => exact (map_zero ((SmoothSingularComparison.realSingularChainMap (coverInclusion hVW)).f n).hom).symm ▸ Submodule.zero_mem _
  | add x y _ _ hx hy => exact (map_add ((SmoothSingularComparison.realSingularChainMap (coverInclusion hVW)).f n).hom x y).symm ▸ Submodule.add_mem _ hx hy
  | smul a x _ hx => exact (map_smul ((SmoothSingularComparison.realSingularChainMap (coverInclusion hVW)).f n).hom a x).symm ▸ Submodule.smul_mem _ a hx

/-- Literal small-chain inclusion for an arbitrary genuine quotient subdomain. -/
abbrev coverSmallInclusionAt (V : Set OrbitSpace) (hV : V ⊆ ⋃ i, U i) :
    coveringSmallChains U hU V hV ⟶ equivariantChains DeckGroup (TopCat.of (CoverOpen V)) :=
  smallInclusion DeckGroup (TopCat.of (CoverOpen V)) (liftedOpenCover U hU V hV)
    (liftedOpenCover_invariant U hU V hV)

instance coverSmallInclusionAt_mono (n : ℕ) : Mono ((coverSmallInclusionAt U hU W hW).f n) :=
  ConcreteCategory.mono_of_injective _ Subtype.val_injective

/-- The genuine graded small-chain map induced by actual subdomain inclusion. -/
def smallSubdomainDegree (n : ℕ) : (coveringSmallChains U hU V hV).X n ⟶
    (coveringSmallChains U hU W hW).X n :=
  Rep.ofHom ⟨((SmoothSingularComparison.realSingularChainMap (coverInclusion hVW)).f n).hom.restrict
    (smallSubdomain_span U hU hV hW hVW n),fun g => by
      apply LinearMap.ext
      intro c
      apply Subtype.ext
      exact congrArg (fun l => l c.val)
        (((equivariantChainMap (coverInclusion hVW) (coverInclusion_equivariant hVW)).f n).hom.isIntertwining' g)⟩

/-- The actual graded small-chain map retains its literal underlying ordinary chain map. -/
theorem smallSubdomainDegree_inclusion (n : ℕ) : smallSubdomainDegree U hU hV hW hVW n ≫
    (coverSmallInclusionAt U hU W hW).f n = (coverSmallInclusionAt U hU V hV).f n ≫
      (equivariantChainMap (coverInclusion hVW) (coverInclusion_equivariant hVW)).f n := rfl

/-- The actual small-chain map on genuine covering subdomains, with all boundaries inherited
through the literal monomorphic small-chain inclusion. -/
def smallSubdomainChains : coveringSmallChains U hU V hV ⟶ coveringSmallChains U hU W hW :=
  complexLiftThroughMono (coverSmallInclusionAt U hU W hW)
    (coverSmallInclusionAt U hU V hV ≫ equivariantChainMap (coverInclusion hVW)
      (coverInclusion_equivariant hVW)) (smallSubdomainDegree U hU hV hW hVW)
        (smallSubdomainDegree_inclusion U hU hV hW hVW)

/-- The genuine small/ordinary inclusion square commutes before taking Hom or homology. -/
theorem smallSubdomainChains_inclusion : smallSubdomainChains U hU hV hW hVW ≫
    coverSmallInclusionAt U hU W hW = coverSmallInclusionAt U hU V hV ≫
      equivariantChainMap (coverInclusion hVW) (coverInclusion_equivariant hVW) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact smallSubdomainDegree_inclusion U hU hV hW hVW n

end TernaryPoly.SmoothSingularGlobal
