module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ScalarSupportCohomology
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ScalarColimit

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits Set SymmetricSpaceCovering TopologicalSpace
variable (A : Rep.{0} ℚ DeckGroup) (n : ℕ)

/-- Genuine compactly supported rational covering singular cohomology. -/
abbrev rationalCoverCompactCohomology := colimit (rationalCoverCompactDiagram A n)

/-- Genuine compactly supported real covering singular cohomology. -/
abbrev realCoverCompactCohomology := colimit (realCoverCompactDiagram A n)

/-- Scalar extension on the actual compact-support colimit. -/
def realCoverCompactInclusion : rationalCoverCompactCohomology A n ⟶
    forgetReal.obj (realCoverCompactCohomology A n) :=
  colim.map (realCoverCompactExtension A n) ≫ colimit.post (realCoverCompactDiagram A n) forgetReal

/-- Compact scalar extension retains the specified actual map on every compact relative class. -/
theorem realCoverCompactInclusion_ι (K : Compacts OrbitSpace) :
    colimit.ι (rationalCoverCompactDiagram A n) K ≫ realCoverCompactInclusion A n =
      realCoverSupportCohomologyInclusion A K n ≫ forgetReal.map (colimit.ι (realCoverCompactDiagram A n) K) :=
  scalarColimit_ι _ _ _ _ K

/-- Literal support-forgetting cocone for actual rational relative singular cohomology. -/
def rationalCoverForgetCocone : Cocone (rationalCoverCompactDiagram A n) where
  pt := (rationalCoverCochains A univ).homology n
  ι := {
    app K := HomologicalComplex.homologyMap (kernel.ι (rationalCoverRestriction A (subset_univ (K : Set OrbitSpace)ᶜ))) n
    naturality K L f := by
      change HomologicalComplex.homologyMap (rationalCoverSupportMap A K L (leOfHom f)) n ≫ _ = _ ≫ 𝟙 _
      rw [Category.comp_id, ← HomologicalComplex.homologyMap_comp, rationalCoverSupportMap_forget] }

/-- Literal support-forgetting cocone for actual real relative singular cohomology. -/
def realCoverForgetCocone : Cocone (realCoverCompactDiagram A n) where
  pt := (cochains DeckGroup (TopCat.of (CoverOpen univ)) (realRep A)).homology n
  ι := {
    app K := HomologicalComplex.homologyMap
      (kernel.ι (coveringCochainRestriction (realRep A).ρ (subset_univ (K : Set OrbitSpace)ᶜ))) n
    naturality K L f := by
      change HomologicalComplex.homologyMap (realCoverSupportMap A K L (leOfHom f)) n ≫ _ = _ ≫ 𝟙 _
      rw [Category.comp_id, ← HomologicalComplex.homologyMap_comp, realCoverSupportMap_forget] }

/-- The actual rational compact-to-ordinary map. -/
def rationalCoverCompactForget : rationalCoverCompactCohomology A n ⟶
    (rationalCoverCochains A univ).homology n :=
  colimit.desc _ (rationalCoverForgetCocone A n)

/-- The actual real compact-to-ordinary map. -/
def realCoverCompactForget : realCoverCompactCohomology A n ⟶
    (cochains DeckGroup (TopCat.of (CoverOpen univ)) (realRep A)).homology n :=
  colimit.desc _ (realCoverForgetCocone A n)

/-- The rational-to-real bridge commutes with the actual compact-to-ordinary map in every degree. -/
theorem realCoverCompact_forget_square :
    rationalCoverCompactForget A n ≫ realSingularCohomologyInclusion DeckGroup (TopCat.of (CoverOpen univ)) A n =
      realCoverCompactInclusion A n ≫ forgetReal.map (realCoverCompactForget A n) :=
  scalarColimit_square _ _ _ _ (rationalCoverForgetCocone A n) (realCoverForgetCocone A n)
    (realSingularCohomologyInclusion DeckGroup (TopCat.of (CoverOpen univ)) A n)
    (fun K => realCoverSupportCohomologyInclusion_forget A K n)

end TernaryPoly.SmoothSingularGlobal
