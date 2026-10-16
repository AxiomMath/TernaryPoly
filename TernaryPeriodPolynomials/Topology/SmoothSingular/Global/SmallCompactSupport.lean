module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteSmallComplex

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory FreeActionLinearization SphereOddDegree
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open scoped Simplicial

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)
  (C : CompactConvexCover)

/-- Literal compact support of an actual small singular cochain: it vanishes on every actual
small simplex lying entirely in the complement of one compact quotient set. -/
def SmallHasCompactSupport (n : ℕ)
    (w : (coveringSmallCochains ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) Set.univ C.covers.ge).X n) : Prop :=
  ∃ K : Set OrbitSpace, IsCompact K ∧ ∀ σ : CoverSmallSimplex
    (fun i => (C.sheet i).quotientDomain) (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n,
      SimplexInDomain Kᶜ σ.val →
        w.hom (coverSmallBasis (fun i => (C.sheet i).quotientDomain)
          (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n σ) = 0

/-- Evaluation of the actual small augmentation on any literal degree-zero flag. -/
theorem smallCechAugmentation_flag_evaluate (n : ℕ)
    (w : (coveringSmallCochains ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) Set.univ C.covers.ge).X n)
    (x : SingularCoverFlag (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n 1) :
    cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen
      (cechDomain (fun i => (C.sheet i).quotientDomain) x.labels))) (Rep.of ρ) n
      (smallCechAugmentationDegree ρ (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n w x.labels)
      (flagSimplex (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n 0 x) =
      w.hom (coverSmallBasis (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n x.point) :=
  (smallCechRestriction_evaluate ρ _ _ _ n 0 x.labels w (flagSimplex _ _ _ n 0 x)).trans
    (congrArg (fun y : SingularCoverFlag (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n 1 =>
        w.hom (coverSmallBasis _ _ _ n y.point)) (localSimplexFlag_flag _ _ _ n 0 x))

/-- Literal compact support of actual small cochains gives finite support of actual chart restrictions. -/
theorem smallCompactSupport_finiteRestriction (n : ℕ)
    (w : (coveringSmallCochains ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) Set.univ C.covers.ge).X n)
    (hw : SmallHasCompactSupport ρ C n w) : w ∈ (finiteRestrictionSmallSubmodules ρ C).term n := by
  obtain ⟨K,hK,hKzero⟩ := hw
  change (familySupport (smallCechAugmentationDegree ρ (fun i => (C.sheet i).quotientDomain)
    (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n w)).Finite
  apply (C.finite_tuples_meeting 1 hK).subset
  intro t ht
  obtain ⟨σ,hσ⟩ := coveringCochain_exists_ne_zero ρ _ ht
  by_contra hn
  have hs : SimplexInDomain Kᶜ (localSimplexFlag (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n 0 t σ).point.val := by
    intro r hr
    exact hn ⟨coordinateProjection (mvSimplexMap σ r).val,(mvSimplexMap σ r).property.2,hr⟩
  apply hσ
  exact (smallCechRestriction_evaluate ρ _ _ _ n 0 t w σ).trans (hKzero _ hs)

/-- Finite actual restriction support forces literal compact support on genuine small simplices. -/
theorem finiteRestriction_smallCompactSupport (n : ℕ)
    (w : (coveringSmallCochains ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) Set.univ C.covers.ge).X n)
    (hw : w ∈ (finiteRestrictionSmallSubmodules ρ C).term n) : SmallHasCompactSupport ρ C n w := by
  let T := familySupport (smallCechAugmentationDegree ρ (fun i => (C.sheet i).quotientDomain)
    (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n w)
  let K : Set OrbitSpace := ⋃ t ∈ T, closure (C.sheet (t 0)).quotientDomain
  have hT : T.Finite := hw
  refine ⟨K,hT.isCompact_biUnion (fun t _ => C.compactClosure (t 0)),?_⟩
  intro σ hσ
  by_contra hn
  let I := smallSimplexIndexCover (fun i => (C.sheet i).quotientDomain)
    (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n
  let x : I.Flag 1 := ⟨fun _ => I.index σ,σ,fun _ => I.index_mem σ⟩
  have hx : x.labels ∈ T := by
    intro hz
    have hv := smallCechAugmentation_flag_evaluate ρ C n w x
    have hzv := congrArg (fun c : (coveringCochains ρ
      (cechDomain (fun i => (C.sheet i).quotientDomain) x.labels)).X n =>
        cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen
          (cechDomain (fun i => (C.sheet i).quotientDomain) x.labels))) (Rep.of ρ) n c
          (flagSimplex _ _ _ n 0 x)) hz
    have hzero := congrArg (fun v => v (flagSimplex _ _ _ n 0 x))
      (map_zero (cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen
        (cechDomain (fun i => (C.sheet i).quotientDomain) x.labels))) (Rep.of ρ) n))
    exact hn (hv.symm.trans (hzv.trans hzero))
  exact hσ (Convexity.StdSimplex.single 0) (mem_iUnion₂.mpr
    ⟨x.labels,hx,subset_closure (x.membership 0 (Convexity.StdSimplex.single 0))⟩)

/-- The auxiliary finite-restriction condition is precisely genuine compact support of actual
small-singular cochains, with complement vanishing as in the relative models. -/
theorem smallCompactSupport_iff_finiteRestriction (n : ℕ)
    (w : (coveringSmallCochains ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) Set.univ C.covers.ge).X n) :
    SmallHasCompactSupport ρ C n w ↔ w ∈ (finiteRestrictionSmallSubmodules ρ C).term n :=
  ⟨smallCompactSupport_finiteRestriction ρ C n w,finiteRestriction_smallCompactSupport ρ C n w⟩

end TernaryPoly.SmoothSingularGlobal
