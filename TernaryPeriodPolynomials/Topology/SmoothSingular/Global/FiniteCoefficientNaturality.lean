module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CompactCoverComparison
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CompactSmoothTotalSquare

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory HomologicalComplex
open Set SmoothCoveringDeRham SymmetricSpaceCovering

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) (C : CompactConvexCover)

/-- The actual finite-support coefficient-to-smooth comparison preserves literal support forgetting. -/
theorem finiteCoefficientSmoothTotalComparison_forget :
    (finiteCoefficientSmoothTotalComparison ρ C).hom ≫ ShortComplex.homologyMap (finiteFormTotalForget ρ C) =
      homologyMap (finiteCoefficientSubmodules ρ C).inclusion 2 ≫ (compactCoverCoefficientSmoothTotal ρ C).hom :=
  verticalAugmentationDegreeTwoIso_naturality (finiteFormSubmodules ρ C).inclusion
    (finiteCoefficientFormTotalAugmentation ρ C)
    (coefficientFormTotalAugmentation ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen))
    (finiteCoefficientFormTotalAugmentation_exactRows ρ C) (compactCoverCoefficientForm_exactRows ρ C)
    (finiteCoefficientSubmodules ρ C).inclusion
    (restrictedVerticalAugmentation_forget (finiteFormSubmodules ρ C) (finiteCoefficientSubmodules ρ C)
      (coefficientFormTotalAugmentation ρ (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen)) (coefficientForm_finiteSupport ρ C))

/-- Literal inclusion from the actual finite-support singular total window. -/
def finiteSingularTotalForget : totalWindow (finiteSingularBicomplex ρ C) ⟶
    totalWindow (singularCechBicomplex ρ (fun i => (C.sheet i).quotientDomain)) :=
  totalWindowMap (finiteSingularSubmodules ρ C).inclusion

omit [FiniteDimensional ℝ F] in
/-- The actual finite coefficient-to-singular comparison commutes with literal support forgetting. -/
theorem finiteCoefficientSingularTotalComparison_forget :
    (finiteCoefficientSingularTotalComparison ρ C).hom ≫ ShortComplex.homologyMap (finiteSingularTotalForget ρ C) =
      homologyMap (finiteCoefficientSubmodules ρ C).inclusion 2 ≫ (compactCoverCoefficientSingularTotal ρ C).hom :=
  verticalAugmentationDegreeTwoIso_naturality (finiteSingularSubmodules ρ C).inclusion
    (finiteCoefficientSingularTotalAugmentation ρ C)
    (coefficientSingularTotalAugmentation ρ (fun i => (C.sheet i).quotientDomain))
    (finiteCoefficientSingularTotalAugmentation_exactRows ρ C) (compactCoverCoefficientSingular_exactRows ρ C)
    (finiteCoefficientSubmodules ρ C).inclusion
    (restrictedVerticalAugmentation_forget (finiteSingularSubmodules ρ C) (finiteCoefficientSubmodules ρ C)
      (coefficientSingularTotalAugmentation ρ (fun i => (C.sheet i).quotientDomain))
        (coefficientSingular_finiteSupport ρ C))

omit [FiniteDimensional ℝ F] in
/-- Actual finite-to-ordinary small cochains commute with the genuine Čech total descent isomorphisms. -/
theorem finiteSmallCechTotalIso_forget :
    (finiteSmallCechTotalIso ρ C).hom ≫ ShortComplex.homologyMap (finiteSingularTotalForget ρ C) =
      homologyMap (finiteRestrictionSmallSubmodules ρ C).inclusion 2 ≫ (compactCoverSmallTotalIso ρ C).hom :=
  augmentationDegreeTwoIso_naturality (finiteSingularSubmodules ρ C).inclusion
    (finiteSmallTotalAugmentation ρ C)
    (singularCechTotalAugmentation ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge)
    (finiteSmallTotalAugmentation_exactRows ρ C)
    (singularCechTotalAugmentation_exactRows ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge)
    (finiteRestrictionSmallSubmodules ρ C).inclusion (finiteSmallColumnAugmentation_forget ρ C)

/-- The actual compact/ordinary smooth arms of the coefficient span commute with compact inclusion. -/
theorem finiteCoefficientCompactSmoothComparison_forget :
    (finiteCoefficientCompactSmoothComparison ρ C).hom ≫ homologyMap (compactInclusion ρ isOpen_univ) 2 =
      homologyMap (finiteCoefficientSubmodules ρ C).inclusion 2 ≫ (compactCoverCoefficientSmooth ρ C).hom :=
  descentComparison_square (finiteCoefficientSmoothTotalComparison ρ C) (compactCoverCoefficientSmoothTotal ρ C)
    (compactFormsCechTotalIso ρ C)
    (globalFormsCechTotalIso ρ (fun i => (C.sheet i).quotientDomain)
      (fun i => (C.sheet i).quotientDomain_isOpen) C.covers.ge)
    (homologyMap (finiteCoefficientSubmodules ρ C).inclusion 2)
    (homologyMap (compactInclusion ρ isOpen_univ) 2) (ShortComplex.homologyMap (finiteFormTotalForget ρ C))
    (finiteCoefficientSmoothTotalComparison_forget ρ C) (compactFormsCechTotalIso_forget ρ C)

omit [FiniteDimensional ℝ F] in
/-- The actual compact/ordinary small-singular arms of the coefficient span commute with support forgetting. -/
theorem finiteCoefficientCompactSmallComparison_forget :
    (finiteCoefficientCompactSmallComparison ρ C).hom ≫ homologyMap (finiteRestrictionSmallSubmodules ρ C).inclusion 2 =
      homologyMap (finiteCoefficientSubmodules ρ C).inclusion 2 ≫ (compactCoverCoefficientSmall ρ C).hom :=
  descentComparison_square (finiteCoefficientSingularTotalComparison ρ C) (compactCoverCoefficientSingularTotal ρ C)
    (finiteSmallCechTotalIso ρ C) (compactCoverSmallTotalIso ρ C)
    (homologyMap (finiteCoefficientSubmodules ρ C).inclusion 2)
    (homologyMap (finiteRestrictionSmallSubmodules ρ C).inclusion 2)
    (ShortComplex.homologyMap (finiteSingularTotalForget ρ C))
    (finiteCoefficientSingularTotalComparison_forget ρ C) (finiteSmallCechTotalIso_forget ρ C)

/-- The genuine compact and ordinary smooth-to-small comparisons satisfy the exact support-forgetting square. -/
theorem compactSmallComparison_forget :
    (compactSmallComparison ρ C).hom ≫ homologyMap (finiteRestrictionSmallSubmodules ρ C).inclusion 2 =
      homologyMap (compactInclusion ρ isOpen_univ) 2 ≫ (compactCoverSmallComparison ρ C).hom :=
  commonSpan_square (finiteCoefficientCompactSmoothComparison ρ C) (finiteCoefficientCompactSmallComparison ρ C)
    (compactCoverCoefficientSmooth ρ C) (compactCoverCoefficientSmall ρ C)
    (homologyMap (finiteCoefficientSubmodules ρ C).inclusion 2)
    (homologyMap (compactInclusion ρ isOpen_univ) 2)
    (homologyMap (finiteRestrictionSmallSubmodules ρ C).inclusion 2)
    (finiteCoefficientCompactSmoothComparison_forget ρ C) (finiteCoefficientCompactSmallComparison_forget ρ C)

end TernaryPoly.SmoothSingularGlobal
