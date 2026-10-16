module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SmallSupportColimit
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ColimitSquare

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory Limits HomologicalComplex TopologicalSpace
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts

variable (A : Rep.{0} ℚ DeckGroup) {ι : Type} (U : ι → Set OrbitSpace)
  (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i)

/-- The literal actual real-relative to small-relative cochain map at a genuine support. -/
abbrev realSupportSmallRestriction (K : Set OrbitSpace) :
    realCoverSupport A K ⟶ smallSupport (realRep A).ρ U hU hcover K :=
  smallRelativeRestriction (realRep A).ρ U hU ((subset_univ Kᶜ).trans hcover) hcover (subset_univ Kᶜ)

/-- Relative small restriction commutes with actual support enlargement before homology. -/
theorem realSupportSmallRestriction_natural (K L : Set OrbitSpace) (hKL : K ⊆ L) :
    realCoverSupportMap A K L hKL ≫ realSupportSmallRestriction A U hU hcover L =
      realSupportSmallRestriction A U hU hcover K ≫ smallSupportMap (realRep A).ρ U hU hcover K L hKL := by
  apply (cancel_mono (kernel.ι (smallSupportRestriction (realRep A).ρ U hU hcover L))).mp
  have hL := smallRelativeRestriction_forget (realRep A).ρ U hU
    ((subset_univ Lᶜ).trans hcover) hcover (subset_univ Lᶜ)
  have hK := smallRelativeRestriction_forget (realRep A).ρ U hU
    ((subset_univ Kᶜ).trans hcover) hcover (subset_univ Kᶜ)
  have hl := (Category.assoc (realCoverSupportMap A K L hKL)
    (realSupportSmallRestriction A U hU hcover L) (kernel.ι (smallSupportRestriction (realRep A).ρ U hU hcover L))).trans
      ((congrArg (fun f => realCoverSupportMap A K L hKL ≫ f) hL).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun f => f ≫ coveringSmallRestriction (realRep A).ρ U hU univ hcover)
            (realCoverSupportMap_forget A K L hKL))))
  have hr := (Category.assoc (realSupportSmallRestriction A U hU hcover K)
    (smallSupportMap (realRep A).ρ U hU hcover K L hKL)
    (kernel.ι (smallSupportRestriction (realRep A).ρ U hU hcover L))).trans
      ((congrArg (fun f => realSupportSmallRestriction A U hU hcover K ≫ f)
        (smallSupportMap_forget (realRep A).ρ U hU hcover K L hKL)).trans hK)
  exact hl.trans hr.symm

/-- Genuine relative subdivision yields an isomorphism of the actual compact-support cohomology diagrams. -/
def realCompactSmallDiagramIso (n : ℕ) :
    realCoverCompactDiagram A n ≅ smallCompactDiagram (realRep A).ρ U hU hcover n :=
  NatIso.ofComponents (fun K => smallRelativeCohomologyIso (realRep A).ρ U hU
    ((subset_univ (K : Set OrbitSpace)ᶜ).trans hcover) hcover (subset_univ (K : Set OrbitSpace)ᶜ) n)
      (fun {K L} f => by
        change homologyMap (realCoverSupportMap A K L (leOfHom f)) n ≫
          homologyMap (realSupportSmallRestriction A U hU hcover L) n =
            homologyMap (realSupportSmallRestriction A U hU hcover K) n ≫
              homologyMap (smallSupportMap (realRep A).ρ U hU hcover K L (leOfHom f)) n
        rw [←homologyMap_comp,←homologyMap_comp,realSupportSmallRestriction_natural])

/-- Actual ordinary-singular and small-singular compact relative colimits are canonically isomorphic. -/
def realCompactSmallIso (n : ℕ) : realCoverCompactCohomology A n ≅
    colimit (smallCompactDiagram (realRep A).ρ U hU hcover n) :=
  colim.mapIso (realCompactSmallDiagramIso A U hU hcover n)

/-- The actual compact relative-colimit comparison retains its literal map at each compact support. -/
theorem realCompactSmallIso_ι (n : ℕ) (K : Compacts OrbitSpace) :
    colimit.ι (realCoverCompactDiagram A n) K ≫ (realCompactSmallIso A U hU hcover n).hom =
      homologyMap (realSupportSmallRestriction A U hU hcover K) n ≫
        colimit.ι (smallCompactDiagram (realRep A).ρ U hU hcover n) K :=
  colimit.ι_map (realCompactSmallDiagramIso A U hU hcover n).hom K

/-- The actual compact relative-colimit comparison commutes with literal support forgetting. -/
theorem realCompactSmallIso_forget (n : ℕ) :
    (realCompactSmallIso A U hU hcover n).hom ≫
      colimit.desc _ (smallCompactForgetCocone (realRep A).ρ U hU hcover n) =
        realCoverCompactForget A n ≫ homologyMap (coveringSmallRestriction (realRep A).ρ U hU univ hcover) n :=
  colimitMap_square _ _ (realCompactSmallDiagramIso A U hU hcover n).hom
    (realCoverForgetCocone A n) (smallCompactForgetCocone (realRep A).ρ U hU hcover n)
    (homologyMap (coveringSmallRestriction (realRep A).ρ U hU univ hcover) n)
    (fun K => smallRelativeCohomologyIso_forget (realRep A).ρ U hU
      ((subset_univ (K : Set OrbitSpace)ᶜ).trans hcover) hcover (subset_univ (K : Set OrbitSpace)ᶜ) n)

variable (C : CompactConvexCover)

/-- The original real compact relative colimit is the actual compact finite-restriction small cohomology. -/
def realCompactFiniteSmallIso (n : ℕ) : realCoverCompactCohomology A n ≅
    (finiteRestrictionSmallComplex (realRep A).ρ C).homology n :=
  realCompactSmallIso A (fun i => (C.sheet i).quotientDomain)
    (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n ≪≫
      smallCompactFiniteIso (realRep A).ρ C n

/-- The bridge from the original compact relative model preserves the exact support-forgetting square. -/
theorem realCompactFiniteSmallIso_forget (n : ℕ) :
    (realCompactFiniteSmallIso A C n).hom ≫
      homologyMap (finiteRestrictionSmallSubmodules (realRep A).ρ C).inclusion n =
        realCoverCompactForget A n ≫ homologyMap (coveringSmallRestriction (realRep A).ρ
          (fun i => (C.sheet i).quotientDomain) (fun i => (C.sheet i).quotientDomain_isOpen)
            univ C.covers.ge) n := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (realCompactSmallIso A (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n).hom ≫ f)
        (smallCompactFiniteIso_forget (realRep A).ρ C n)).trans
          (realCompactSmallIso_forget A (fun i => (C.sheet i).quotientDomain)
            (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge n))

end TernaryPoly.SmoothSingularGlobal
