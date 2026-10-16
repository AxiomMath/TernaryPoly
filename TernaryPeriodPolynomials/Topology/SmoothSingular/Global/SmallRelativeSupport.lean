module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SmallRelativeComparison
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SmallCompactSupport

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory FreeActionLinearization SphereOddDegree Module
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open scoped Simplicial

variable {ι : Type} (U : ι → Set OrbitSpace) (hU : ∀ i, IsOpen (U i))
  (hcover : Set.univ ⊆ ⋃ i, U i) (V : Set OrbitSpace)

/-- Actual small singular simplices in a genuine covering subdomain. -/
abbrev CoverSmallSimplexAt (n : ℕ) :=
  {σ : SingularSimplex (TopCat.of (CoverOpen V)) n //
    IsSmallSimplex (liftedOpenCover U hU V ((subset_univ V).trans hcover)) σ}

/-- Inclusion of a genuine subdomain-small simplex into the genuine global small family. -/
def globalizeSmallSimplex (n : ℕ) (σ : CoverSmallSimplexAt U hU hcover V n) :
    CoverSmallSimplex U hU hcover n :=
  ⟨globalizeSimplex V n σ.val,includeSubdomainSimplex_small U hU ((subset_univ V).trans hcover)
    hcover (subset_univ V) n σ.val σ.property⟩

/-- The actual small-chain restriction map acts literally on the genuine subtype-indexed basis. -/
theorem smallSubdomainDegree_basis (n : ℕ) (σ : CoverSmallSimplexAt U hU hcover V n) :
    (smallSubdomainDegree U hU ((subset_univ V).trans hcover) hcover (subset_univ V) n).hom
      (predicateBasis (TopCat.of (CoverOpen V)) n
        (IsSmallSimplex (liftedOpenCover U hU V ((subset_univ V).trans hcover))) σ) =
      coverSmallBasis U hU hcover n (globalizeSmallSimplex U hU hcover V n σ) := by
  apply Subtype.ext
  have h₁ := congrArg (((SmoothSingularComparison.realSingularChainMap (coverInclusion (subset_univ V))).f n).hom)
    (predicateBasis_apply (TopCat.of (CoverOpen V)) n
      (IsSmallSimplex (liftedOpenCover U hU V ((subset_univ V).trans hcover))) σ)
  have h₂ := congrArg (fun f => f.hom 1) (singularGenerator_map (coverInclusion (subset_univ V)) n σ.val)
  exact h₁.trans (h₂.trans (predicateBasis_apply (TopCat.of (CoverOpen univ)) n
    (IsSmallSimplex (liftedOpenCover U hU univ hcover)) (globalizeSmallSimplex U hU hcover V n σ)).symm)

/-- Restricting a global small simplex into a genuine quotient subdomain preserves smallness. -/
def restrictGlobalSmallSimplex (n : ℕ) (σ : CoverSmallSimplex U hU hcover n)
    (hσ : SimplexInDomain V σ.val) : CoverSmallSimplexAt U hU hcover V n := by
  refine ⟨restrictGlobalSimplex V n σ.val hσ,?_⟩
  obtain ⟨i,hi⟩ := (coveringSimplex_small_iff U hU univ hcover σ.val).mp σ.property
  apply (coveringSimplex_small_iff U hU V ((subset_univ V).trans hcover) _).mpr
  refine ⟨i,fun r => ?_⟩
  rw [restrictGlobalSimplex_value]
  exact hi r

/-- Globalizing the restricted small simplex recovers the same literal global small simplex. -/
theorem globalize_restrictGlobalSmallSimplex (n : ℕ) (σ : CoverSmallSimplex U hU hcover n)
    (hσ : SimplexInDomain V σ.val) :
    globalizeSmallSimplex U hU hcover V n (restrictGlobalSmallSimplex U hU hcover V n σ hσ) = σ :=
  Subtype.ext (globalize_restrictSimplex V n σ.val hσ)

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)

/-- On each actual local small-simplex generator, restriction is literal globalization. -/
theorem smallSubdomainRestriction_basis (n : ℕ)
    (w : (coveringSmallCochains ρ U hU univ hcover).X n)
    (σ : CoverSmallSimplexAt U hU hcover V n) :
    ((smallSubdomainRestriction ρ U hU ((subset_univ V).trans hcover) hcover (subset_univ V)).f n w).hom
      (predicateBasis (TopCat.of (CoverOpen V)) n
        (IsSmallSimplex (liftedOpenCover U hU V ((subset_univ V).trans hcover))) σ) =
      w.hom (coverSmallBasis U hU hcover n (globalizeSmallSimplex U hU hcover V n σ)) :=
  congrArg w.hom (smallSubdomainDegree_basis U hU hcover V n σ)

/-- Zero restriction is exactly vanishing on the actual small simplices contained in the subdomain. -/
theorem smallSubdomainRestriction_zero_iff (n : ℕ)
    (w : (coveringSmallCochains ρ U hU univ hcover).X n) :
    (smallSubdomainRestriction ρ U hU ((subset_univ V).trans hcover) hcover (subset_univ V)).f n w = 0 ↔
      ∀ σ : CoverSmallSimplex U hU hcover n, SimplexInDomain V σ.val →
        w.hom (coverSmallBasis U hU hcover n σ) = 0 := by
  constructor
  · intro hw σ hσ
    let τ := restrictGlobalSmallSimplex U hU hcover V n σ hσ
    have h := smallSubdomainRestriction_basis U hU hcover V ρ n w τ
    rw [globalize_restrictGlobalSmallSimplex] at h
    exact h.symm.trans (congrArg (fun c => c.hom
      (predicateBasis (TopCat.of (CoverOpen V)) n
        (IsSmallSimplex (liftedOpenCover U hU V ((subset_univ V).trans hcover))) τ)) hw)
  · intro hw
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply (predicateBasis (TopCat.of (CoverOpen V)) n
      (IsSmallSimplex (liftedOpenCover U hU V ((subset_univ V).trans hcover)))).ext
    intro σ
    exact (smallSubdomainRestriction_basis U hU hcover V ρ n w σ).trans
      (hw (globalizeSmallSimplex U hU hcover V n σ) (globalizeSimplex_mem V n σ.val))

/-- The finite-restriction compact small model is exactly the union of actual complement kernels. -/
theorem finiteRestriction_iff_exists_complement_kernel (C : CompactConvexCover) (n : ℕ)
    (w : (coveringSmallCochains ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) univ C.covers.ge).X n) :
    w ∈ (finiteRestrictionSmallSubmodules ρ C).term n ↔
      ∃ K : TopologicalSpace.Compacts OrbitSpace,
        (smallSubdomainRestriction ρ (fun i => (C.sheet i).quotientDomain)
          (fun i => (C.sheet i).quotientDomain_isOpen)
          ((subset_univ (K : Set OrbitSpace)ᶜ).trans C.covers.ge) C.covers.ge
          (subset_univ (K : Set OrbitSpace)ᶜ)).f n w = 0 := by
  rw [←smallCompactSupport_iff_finiteRestriction]
  constructor
  · rintro ⟨K,hK,hw⟩
    exact ⟨⟨K,hK⟩,(smallSubdomainRestriction_zero_iff _ _ _ _ ρ n w).mpr hw⟩
  · rintro ⟨K,hw⟩
    exact ⟨K,K.isCompact,(smallSubdomainRestriction_zero_iff _ _ _ _ ρ n w).mp hw⟩

end TernaryPoly.SmoothSingularGlobal
