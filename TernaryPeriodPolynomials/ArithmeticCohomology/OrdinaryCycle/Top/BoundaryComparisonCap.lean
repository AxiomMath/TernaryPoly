module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonOrdinaryIso
public import TernaryPeriodPolynomials.GroupCohomology.HomCokernelKernelIso
public import TernaryPeriodPolynomials.SymmetricSpace.All.TopBoundaryCap

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryTopBoundaryComparison
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence
open EquivariantSingularSmall SingularBoundaryRestriction SingularLocalHomology
open CompactInteriorRelativeBoundary SymmetricSpaceRelativeCapConnecting

variable (W : Rep.{0} ℚ principalSix)

/-- Hom pullback along the actual boundary chain map is the actual boundary restriction. -/
theorem upstairsHomPullback_eq_boundaryRestriction :
    homPullback upstairsBoundaryChainMap W = boundaryRestriction W := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

/-- Actual relative Hom cochains equal the actual equivariant restriction kernel. -/
def relativeHomKernelIso : homCochains upstairsRelativeChains W ≅ relativeCochains W :=
  HomCokernelKernel.cochainIso upstairsBoundaryChainMap W ≪≫
    kernelIsoOfEq (upstairsHomPullback_eq_boundaryRestriction W)

/-- Actual relative Hom cochains and actual geometric relative cochains are identified using
literal quotient descent, restriction kernels, and the covering comparison. -/
def relativeHomGeometricIso : homCochains upstairsRelativeChains W ≅ geometricRelativeCochains W :=
  relativeHomKernelIso W ≪≫ boundaryGeometricIso W

/-- The actual cap isomorphism from relative Hom cohomology to genuine bordified H3. -/
def relativeHomCapIso : (homCochains upstairsRelativeChains W).homology 2 ≅
    (bordifiedLocalChains W).homology 3 := by
  exact (homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) 2).mapIso (relativeHomGeometricIso W) ≪≫
    @asIso _ _ _ _ (relativeFundamentalCap W) (SymmetricSpaceAllTopBoundary.relativeFundamentalCap_isIso W)

/-- The relative Hom cap map is precisely the geometric comparison followed by the actual
fixed-fundamental-class cap product. -/
theorem relativeHomCapIso_hom : (relativeHomCapIso W).hom =
    homologyMap (relativeHomGeometricIso W).hom 2 ≫ relativeFundamentalCap W := rfl

/-- The genuine arithmetic group H3-to-ordinary-functional isomorphism, with canonical
relative evaluation and the actual connecting/MV comparison. -/
def groupOrdinaryIso : groupHomology W 3 ≅ ordinaryFunctionals W :=
  bordifiedGroupLocalHomologyIso W 3 ≪≫ (relativeHomCapIso W).symm ≪≫
    relativeOrdinaryCohomologyIso W

/-- The top comparison recovers canonical ordinary evaluation on each actual capped class. -/
theorem cappedClass_groupOrdinary :
    (relativeHomCapIso W).hom ≫ (bordifiedGroupLocalHomologyIso W 3).inv ≫
      (groupOrdinaryIso W).hom = (relativeOrdinaryCohomologyIso W).hom := by
  simp only [groupOrdinaryIso, Iso.trans_hom, Iso.symm_hom,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

end TernaryPoly.OrdinaryTopBoundaryComparison
