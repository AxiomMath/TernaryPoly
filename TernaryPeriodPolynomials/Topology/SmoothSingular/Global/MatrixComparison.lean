module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CoordinateCompact
public import TernaryPeriodPolynomials.SymmetricSpace.SingularOrbits

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits Set SymmetricSpaceCovering
open SingularLocalCoefficient SingularLocalSupport SingularLocalCompactDuality CompactInteriorRelativeBoundary

/-- The matrix quotient is exactly the preserved original singular-covering projection. -/
theorem matrixQuotientProjection_eq :
    matrixQuotientProjection = SymmetricSpaceCovering.singularCoveringProjection := rfl

variable (A : Rep.{0} ℚ DeckGroup)

/-- The actual matrix-quotient cochain model is the rational coordinate Hom model. -/
def matrixCoordinateCochainIso :
    localCochains matrixQuotientProjection matrixQuotientCoverFact.out A ≅ rationalCoverCochains A univ := by
  have := coveringCochainMap_isIso coordinateMatrixCoverHomeomorph A
  exact asIso (coveringCochainMap coordinateMatrixCoverHomeomorph A) ≪≫ (rationalCoverGlobalLocalIso A).symm

/-- The same literal geometric comparison on ordinary cohomology in every degree. -/
def matrixCoordinateCohomologyIso (n : ℕ) :
    (localCochains matrixQuotientProjection matrixQuotientCoverFact.out A).homology n ≅
      (rationalCoverCochains A univ).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapIso (matrixCoordinateCochainIso A)

/-- The matrix-quotient compact cohomology is the actual coordinate support-colimit model. -/
def matrixCoordinateCompactIso (n : ℕ) :
    compactCohomology matrixQuotientProjection A n ≅ rationalCoverCompactCohomology A n :=
  coveringCompactIso coordinateMatrixCoverHomeomorph A n ≪≫ (coordinateCompactLocalIso A n).symm

/-- Inverse coordinate/local transport retains literal support forgetting. -/
theorem coordinateCompactLocalIso_inv_forget (n : ℕ) :
    (coordinateCompactLocalIso A n).inv ≫ rationalCoverCompactForget A n =
      compactForget (coverProjection univ) A n ≫
        HomologicalComplex.homologyMap (rationalCoverGlobalLocalIso A).inv n := by
  apply (cancel_epi (coordinateCompactLocalIso A n).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Category.assoc,
    coordinateCompactLocalIso_forget, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, Iso.hom_inv_id, HomologicalComplex.homologyMap_id, Category.comp_id]

/-- The actual original-matrix and coordinate compact-to-ordinary maps form a commuting square. -/
theorem matrixCoordinate_forget (n : ℕ) :
    (matrixCoordinateCompactIso A n).hom ≫ rationalCoverCompactForget A n =
      compactForget matrixQuotientProjection A n ≫ (matrixCoordinateCohomologyIso A n).hom := by
  unfold matrixCoordinateCompactIso
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, coordinateCompactLocalIso_inv_forget,
    ← Category.assoc, coveringCompactIso_forget, Category.assoc]
  exact congrArg (fun k => compactForget matrixQuotientProjection A n ≫ k)
    (HomologicalComplex.homologyMap_comp (coveringCochainMap coordinateMatrixCoverHomeomorph A)
      (rationalCoverGlobalLocalIso A).inv n).symm

/-- Actual rational-to-real ordinary comparison from the matrix-quotient local model. -/
def matrixRealCohomologyInclusion (n : ℕ) :
    (localCochains matrixQuotientProjection matrixQuotientCoverFact.out A).homology n ⟶
      forgetReal.obj ((cochains DeckGroup (TopCat.of (CoverOpen univ)) (realRep A)).homology n) :=
  (matrixCoordinateCohomologyIso A n).hom ≫
    realSingularCohomologyInclusion DeckGroup (TopCat.of (CoverOpen univ)) A n

/-- Actual rational-to-real compact comparison from the matrix-quotient support colimit. -/
def matrixRealCompactInclusion (n : ℕ) :
    compactCohomology matrixQuotientProjection A n ⟶ forgetReal.obj (realCoverCompactCohomology A n) :=
  (matrixCoordinateCompactIso A n).hom ≫ realCoverCompactInclusion A n

/-- The complete actual rational-to-real bridge commutes with the compactForget map. -/
theorem matrixReal_compact_square (n : ℕ) :
    compactForget matrixQuotientProjection A n ≫ matrixRealCohomologyInclusion A n =
      matrixRealCompactInclusion A n ≫ forgetReal.map (realCoverCompactForget A n) := by
  unfold matrixRealCohomologyInclusion matrixRealCompactInclusion
  rw [← Category.assoc, ← matrixCoordinate_forget, Category.assoc, realCoverCompact_forget_square]
  exact (Category.assoc _ _ _).symm

/-- Real covering cohomology detects every class of the rational matrix-quotient model. -/
theorem matrixRealCohomologyInclusion_injective (n : ℕ) :
    Function.Injective (matrixRealCohomologyInclusion A n) :=
  (realSingularCohomology_injective DeckGroup (TopCat.of (CoverOpen univ)) A n).comp
    (ConcreteCategory.bijective_of_isIso (matrixCoordinateCohomologyIso A n).hom).1

end TernaryPoly.SmoothSingularGlobal
