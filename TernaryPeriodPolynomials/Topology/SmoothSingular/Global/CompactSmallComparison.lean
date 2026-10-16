module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteCoefficientFormExact
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteCoefficientSingularExact
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteFormTotalExact
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteSmallTotalExact
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.SmallCompactSupport

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory
open SmoothCoveringDeRham SymmetricSpaceCovering

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) (C : CompactConvexCover)

/-- Actual finite-support common coefficient cohomology computes the supported smooth total. -/
def finiteCoefficientSmoothTotalComparison : (finiteCoefficientCechComplex ρ C).homology 2 ≅
    (totalWindow (finiteFormBicomplex ρ C)).homology :=
  (finiteCoefficientCechComplex ρ C).homologyIsoSc' 1 2 3 (by simp) (by simp) ≪≫
    (finiteCoefficientFormTotalAugmentation ρ C).totalAugmentationHomologyIso
      (finiteCoefficientFormTotalAugmentation_exactRows ρ C) ≪≫
    (totalFlipHomologyIso (finiteFormBicomplex ρ C)).symm

/-- The same actual finite-support common coefficient cohomology computes the supported singular total. -/
def finiteCoefficientSingularTotalComparison : (finiteCoefficientCechComplex ρ C).homology 2 ≅
    (totalWindow (finiteSingularBicomplex ρ C)).homology :=
  (finiteCoefficientCechComplex ρ C).homologyIsoSc' 1 2 3 (by simp) (by simp) ≪≫
    (finiteCoefficientSingularTotalAugmentation ρ C).totalAugmentationHomologyIso
      (finiteCoefficientSingularTotalAugmentation_exactRows ρ C) ≪≫
    (totalFlipHomologyIso (finiteSingularBicomplex ρ C)).symm

/-- Genuine compact smooth cohomology is computed by the actual finite coefficient Čech complex. -/
def finiteCoefficientCompactSmoothComparison : (finiteCoefficientCechComplex ρ C).homology 2 ≅
    (globalCompactComplex ρ).homology 2 :=
  finiteCoefficientSmoothTotalComparison ρ C ≪≫ (compactFormsCechTotalIso ρ C).symm

/-- Genuine compact small-singular cohomology is computed by the same finite coefficient Čech complex.
The complement-vanishing meaning of the source model was separately proved. -/
def finiteCoefficientCompactSmallComparison : (finiteCoefficientCechComplex ρ C).homology 2 ≅
    (finiteRestrictionSmallComplex ρ C).homology 2 :=
  finiteCoefficientSingularTotalComparison ρ C ≪≫ (finiteSmallCechTotalIso ρ C).symm

/-- Actual compact smooth-to-small-singular comparison, obtained through genuine supported
Čech spans and proved actual local primitives. The original relative-colimit bridge is separate. -/
def compactSmallComparison : (globalCompactComplex ρ).homology 2 ≅
    (finiteRestrictionSmallComplex ρ C).homology 2 :=
  (finiteCoefficientCompactSmoothComparison ρ C).symm ≪≫ finiteCoefficientCompactSmallComparison ρ C

/-- This compact comparison is induced by the actual finite common coefficient span. -/
theorem compactSmallComparison_coefficient_square :
    (finiteCoefficientCompactSmoothComparison ρ C).hom ≫ (compactSmallComparison ρ C).hom =
      (finiteCoefficientCompactSmallComparison ρ C).hom := by
  simp [compactSmallComparison]

end TernaryPoly.SmoothSingularGlobal
