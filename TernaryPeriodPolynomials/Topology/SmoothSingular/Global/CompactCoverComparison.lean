module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CompactCoverColumnExact
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.VerticalNaturality
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CompactSmallComparison

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory HomologicalComplex
open SmoothCoveringDeRham SymmetricSpaceCovering

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) (C : CompactConvexCover)

/-- The actual coefficient Čech complex on the chosen compact convex cover computes smooth total H². -/
def compactCoverCoefficientSmoothTotal :
    (coefficientCechComplex ρ (fun i => (C.sheet i).quotientDomain)).homology 2 ≅
      (totalWindow (formCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen))).homology :=
  verticalAugmentationDegreeTwoIso (coefficientFormTotalAugmentation ρ
    (fun i => (C.sheet i).quotientDomain) (fun i => (C.sheet i).quotientDomain_isOpen))
      (compactCoverCoefficientForm_exactRows ρ C)

/-- The same actual coefficient Čech complex computes the genuine singular total H². -/
def compactCoverCoefficientSingularTotal :
    (coefficientCechComplex ρ (fun i => (C.sheet i).quotientDomain)).homology 2 ≅
      (totalWindow (singularCechBicomplex ρ (fun i => (C.sheet i).quotientDomain))).homology :=
  verticalAugmentationDegreeTwoIso (coefficientSingularTotalAugmentation ρ
    (fun i => (C.sheet i).quotientDomain)) (compactCoverCoefficientSingular_exactRows ρ C)

/-- Actual small cohomology computes the singular total on this same genuine compact convex cover. -/
def compactCoverSmallTotalIso :
    (coveringSmallCochains ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) univ C.covers.ge).homology 2 ≅
        (totalWindow (singularCechBicomplex ρ (fun i => (C.sheet i).quotientDomain))).homology :=
  augmentationDegreeTwoIso (singularCechTotalAugmentation ρ (fun i => (C.sheet i).quotientDomain)
    (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge)
      (singularCechTotalAugmentation_exactRows ρ (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge)

/-- The actual common coefficient span on the compact convex cover computes ordinary smooth H². -/
def compactCoverCoefficientSmooth :
    (coefficientCechComplex ρ (fun i => (C.sheet i).quotientDomain)).homology 2 ≅
      (globalComplex ρ).homology 2 :=
  compactCoverCoefficientSmoothTotal ρ C ≪≫
    (globalFormsCechTotalIso ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge).symm

/-- The same actual common coefficient span computes ordinary small-singular H². -/
def compactCoverCoefficientSmall :
    (coefficientCechComplex ρ (fun i => (C.sheet i).quotientDomain)).homology 2 ≅
      (coveringSmallCochains ρ (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen) univ C.covers.ge).homology 2 :=
  compactCoverCoefficientSingularTotal ρ C ≪≫ (compactCoverSmallTotalIso ρ C).symm

/-- The ordinary genuine smooth-to-small comparison uses the same cover as the compact comparison. -/
def compactCoverSmallComparison : (globalComplex ρ).homology 2 ≅
    (coveringSmallCochains ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) univ C.covers.ge).homology 2 :=
  (compactCoverCoefficientSmooth ρ C).symm ≪≫ compactCoverCoefficientSmall ρ C

/-- Genuine global smooth/singular H² comparison through the actual common compact-convex-cover span. -/
def compactCoverGlobalComparison : (globalComplex ρ).homology 2 ≅ (coveringCochains ρ univ).homology 2 := by
  let := coveringSmallRestriction_quasiIso ρ (fun i => (C.sheet i).quotientDomain)
    (fun i => (C.sheet i).quotientDomain_isOpen) univ C.covers.ge
  exact compactCoverSmallComparison ρ C ≪≫
    (isoOfQuasiIsoAt (coveringSmallRestriction ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) univ C.covers.ge) 2).symm

/-- The actual ordinary global comparison retains the literal small restriction on cohomology. -/
theorem compactCoverGlobalComparison_small :
    (compactCoverGlobalComparison ρ C).hom ≫ homologyMap (coveringSmallRestriction ρ
      (fun i => (C.sheet i).quotientDomain) (fun i => (C.sheet i).quotientDomain_isOpen) univ C.covers.ge) 2 =
        (compactCoverSmallComparison ρ C).hom := by
  let := coveringSmallRestriction_quasiIso ρ (fun i => (C.sheet i).quotientDomain)
    (fun i => (C.sheet i).quotientDomain_isOpen) univ C.covers.ge
  dsimp only [compactCoverGlobalComparison,Iso.trans_hom,Iso.symm_hom]
  rw [Category.assoc]
  exact (congrArg (fun f => (compactCoverSmallComparison ρ C).hom ≫ f)
    (isoOfQuasiIsoAt (coveringSmallRestriction ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) univ C.covers.ge) 2).inv_hom_id).trans (Category.comp_id _)

end TernaryPoly.SmoothSingularGlobal
