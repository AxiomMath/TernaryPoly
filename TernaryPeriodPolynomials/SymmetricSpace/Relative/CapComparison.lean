module

public import TernaryPeriodPolynomials.SymmetricSpace.Relative.CapInterior
public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundaryComplement

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceRelativeCap
open CategoryTheory HomologicalComplex TopologicalSpace
open SymmetricSpaceBordifiedPrincipalSix SymmetricSpaceBordifiedQuotient IntegralGL3Congruence
open SymmetricSpaceRelativeFundamental SingularBoundaryRestriction
open SingularLocalSupport SingularLocalCompactCap EquivariantSingularSmall
open CompactInteriorRelativeBoundary

variable (V : Rep.{0} ℚ principalSix)

/-- At every ambient compact interior support, the class-in-open formula identifies the two
actual cap maps before passing to the compact-support colimit. -/
theorem classInOpen_cap (K : Compacts (TopCat.of BordifiedOrbit))
    (hKA : (K : Set BordifiedOrbit) ⊆ (boundary principalSix)ᶜ)
    (a b : ℕ) (hab : a+b = 5) :
    classInOpen wholeProjection V boundaryComplementOpen K hKA a ≫
      interiorCapToBordified V a b hab =
    homologyMap (supportMap wholeProjection V K (boundary principalSix)ᶜ hKA) a ≫
      relativeCapMap V a b hab := by
  unfold classInOpen interiorCapToBordified
  erw [Category.assoc,← Category.assoc (compactClassMap _ _ _ _) _,compactCapMap_classMap]
  exact (relativeCapMap_support V K K.isCompact hKA a b hab).symm

/-- The literal compact-to-boundary-support comparison identifies actual relative cap with
actual interior compact cap followed by actual local-homology inclusion. -/
theorem compactBoundarySupportIso_cap (a b : ℕ) (hab : a+b = 5) :
    (compactBoundarySupportIso V a).hom ≫ relativeCapMap V a b hab =
      interiorCapToBordified V a b hab := by
  apply compactCohomology_hom_ext
  intro K
  apply (cancel_epi (openSupportIso wholeProjection V boundaryComplementOpen K a).hom).mp
  have hc := congrArg (fun f => f ≫ interiorCapToBordified V a b hab)
    (classInOpen_image wholeProjection V boundaryComplementOpen K a)
  have hp := classInOpen_cap V (openCompactImage boundaryComplementOpen K)
    (openCompactImage_subset boundaryComplementOpen K) a b hab
  have hright := hc.symm.trans hp
  change _ = (openSupportIso wholeProjection V boundaryComplementOpen K a).hom ≫
    compactClassMap interiorProjection V K a ≫ interiorCapToBordified V a b hab
  have hright' : (openSupportIso wholeProjection V boundaryComplementOpen K a).hom ≫
      compactClassMap interiorProjection V K a ≫ interiorCapToBordified V a b hab =
      homologyMap (supportMap wholeProjection V (openCompactImage boundaryComplementOpen K)
        (boundary principalSix)ᶜ (openCompactImage_subset boundaryComplementOpen K)) a ≫
          relativeCapMap V a b hab := by
    exact (Category.assoc _ _ _).symm.trans hright
  apply Eq.trans ?_ hright'.symm
  erw [← Category.assoc (compactClassMap _ _ _ _),compactBoundarySupportIso_classMap,
    Category.assoc,Iso.hom_inv_id_assoc]

/-- Poincare--Lefschetz duality for the actual arithmetic compact bordification: the literal
relative cap with its genuine fundamental class is an isomorphism in every complementary degree. -/
theorem relativeCapMap_isIso (a b : ℕ) (hab : a+b = 5) :
    IsIso (relativeCapMap V a b hab) := by
  have : IsIso ((compactBoundarySupportIso V a).hom ≫ relativeCapMap V a b hab) := by
    erw [compactBoundarySupportIso_cap]
    exact interiorCapToBordified_isIso V a b hab
  exact IsIso.of_isIso_comp_left (compactBoundarySupportIso V a).hom (relativeCapMap V a b hab)

/-- The actual relative cap isomorphism, with no orientation or comparison hypothesis. -/
def relativeCapIso (a b : ℕ) (hab : a+b = 5) :
    (supportCochains wholeProjection V (boundary principalSix)ᶜ).homology a ≅
      (coveringLocalChains wholeProjection V).homology b := by
  have := relativeCapMap_isIso V a b hab
  exact asIso (relativeCapMap V a b hab)

@[simp] theorem relativeCapIso_hom (a b : ℕ) (hab : a+b = 5) :
    (relativeCapIso V a b hab).hom = relativeCapMap V a b hab := rfl

end TernaryPoly.SymmetricSpaceRelativeCap
