module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CoordinateSupport
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ScalarCompact
public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundaryForget

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits Set TopologicalSpace SymmetricSpaceCovering
open SingularLocalSupport CompactInteriorRelativeBoundary
variable (A : Rep.{0} ℚ DeckGroup)

/-- The actual coordinate/local fixed-support isomorphisms form a compact-support diagram isomorphism. -/
def coordinateCompactLocalDiagramIso (n : ℕ) :
    rationalCoverCompactDiagram A n ≅ compactCohomologyDiagram (coverProjection univ) A n :=
  NatIso.ofComponents
    (fun K => (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapIso
      (coordinateSupportLocalIso A K)) (fun {K L} f => by
        change HomologicalComplex.homologyMap (rationalCoverSupportMap A K L (leOfHom f)) n ≫
          HomologicalComplex.homologyMap (coordinateSupportLocalIso A L).hom n =
            HomologicalComplex.homologyMap (coordinateSupportLocalIso A K).hom n ≫
              HomologicalComplex.homologyMap (supportMap (coverProjection univ) A K L (leOfHom f)) n
        rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
          coordinateSupportLocalIso_natural])

/-- Actual compactly supported coordinate Hom cohomology is the fiber-valued local cohomology. -/
def coordinateCompactLocalIso (n : ℕ) :
    rationalCoverCompactCohomology A n ≅ compactCohomology (coverProjection univ) A n :=
  colim.mapIso (coordinateCompactLocalDiagramIso A n)

/-- The compact comparison retains its actual map on every compact-support relative class. -/
theorem coordinateCompactLocalIso_ι (K : Compacts OrbitSpace) (n : ℕ) :
    colimit.ι (rationalCoverCompactDiagram A n) K ≫ (coordinateCompactLocalIso A n).hom =
      HomologicalComplex.homologyMap (coordinateSupportLocalIso A K).hom n ≫
        compactClassMap (coverProjection univ) A K n :=
  colimit.ι_map (coordinateCompactLocalDiagramIso A n).hom K

/-- The actual coordinate rational support-forgetting map is literal on each fixed support. -/
theorem rationalCoverCompactForget_ι (K : Compacts OrbitSpace) (n : ℕ) :
    colimit.ι (rationalCoverCompactDiagram A n) K ≫ rationalCoverCompactForget A n =
      HomologicalComplex.homologyMap (kernel.ι (rationalCoverRestriction A (subset_univ (K : Set OrbitSpace)ᶜ))) n :=
  colimit.ι_desc _ _

/-- Fixed-support local transport preserves the literal ordinary cohomology map. -/
theorem coordinateSupportLocalIso_homology_forget (K : Set OrbitSpace) (n : ℕ) :
    HomologicalComplex.homologyMap (coordinateSupportLocalIso A K).hom n ≫
        HomologicalComplex.homologyMap (supportInclusion (coverProjection univ) A K) n =
      HomologicalComplex.homologyMap (kernel.ι (rationalCoverRestriction A (subset_univ Kᶜ))) n ≫
        HomologicalComplex.homologyMap (rationalCoverGlobalLocalIso A).hom n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun k => HomologicalComplex.homologyMap k n) (coordinateSupportLocalIso_forget A K)).trans
      (HomologicalComplex.homologyMap_comp _ _ n))

/-- The actual coordinate/local compact comparison preserves the genuine compactForget map. -/
theorem coordinateCompactLocalIso_forget (n : ℕ) :
    (coordinateCompactLocalIso A n).hom ≫ compactForget (coverProjection univ) A n =
      rationalCoverCompactForget A n ≫ HomologicalComplex.homologyMap (rationalCoverGlobalLocalIso A).hom n := by
  apply colimit.hom_ext
  intro K
  erw [← Category.assoc, coordinateCompactLocalIso_ι, Category.assoc, compactForget_classMap,
    ← Category.assoc, rationalCoverCompactForget_ι]
  exact coordinateSupportLocalIso_homology_forget A K n

end TernaryPoly.SmoothSingularGlobal
