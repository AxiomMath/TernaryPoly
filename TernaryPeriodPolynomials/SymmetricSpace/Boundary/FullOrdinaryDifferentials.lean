module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullOrdinaryCoordinates

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory HomologicalComplex EquivariantSingularSmall OrdinaryParabolicGroups groupCohomology

variable (W : Rep.{0} ℚ ModThreeGoodAction.IntegralGL)

/-- The canonical full geometric cone differential is exactly the ordinary P/Q/B d0. -/
theorem ordinaryCoordinates_d0 (c : canonicalFaceCone.X 0 ⟶ W) :
    ordinaryCoordinates1 W (canonicalFaceCone.d 1 0 ≫ c) =
      OrdinaryBoundaryCone.d0 W P Q (ordinaryCoordinates0 W c) := by
  rw [ordinaryCoordinates1_apply,ordinaryCoordinates0_apply]
  apply Prod.ext
  · change inducedCoordinates1 P W (canonicalPlaneCochain W 1 _) = _
    rw [canonicalPlaneCochain_d,inducedCoordinates_d0]
    rfl
  apply Prod.ext
  · change inducedCoordinates1 Q W (canonicalLineCochain W 1 _) = _
    rw [canonicalLineCochain_d,inducedCoordinates_d0]
    rfl
  change -inducedCoordinates0 B W (canonicalCornerCochain W 0 _) =
    inducedCoordinates0 P W (canonicalPlaneCochain W 0 c) -
      inducedCoordinates0 Q W (canonicalLineCochain W 0 c)
  rw [canonicalCornerCochain_d0,map_sub]
  have hl := inducedCoordinates_restrict0 B W Q fullB_le_Q (canonicalLineCochain W 0 c)
  have hp := inducedCoordinates_restrict0 B W P fullB_le_P (canonicalPlaneCochain W 0 c)
  change inducedCoordinates0 B W (canonicalLineArrow.f 0 ≫ canonicalLineCochain W 0 c) = _ at hl
  change inducedCoordinates0 B W (canonicalPlaneArrow.f 0 ≫ canonicalPlaneCochain W 0 c) = _ at hp
  rw [hl,hp,neg_sub]

/-- The shifted corner sign converts line-minus-plane into the ordinary P-minus-Q compatibility. -/
theorem ordinaryCoordinates_d1 (c : canonicalFaceCone.X 1 ⟶ W) :
    ordinaryCoordinates2 W (canonicalFaceCone.d 2 1 ≫ c) =
      OrdinaryBoundaryCone.d1 W P Q (ordinaryCoordinates1 W c) := by
  rw [ordinaryCoordinates2_apply,ordinaryCoordinates1_apply]
  apply Prod.ext
  · change inducedCoordinates2 P W (canonicalPlaneCochain W 2 _) = _
    rw [canonicalPlaneCochain_d,inducedCoordinates_d1]
    rfl
  apply Prod.ext
  · change inducedCoordinates2 Q W (canonicalLineCochain W 2 _) = _
    rw [canonicalLineCochain_d,inducedCoordinates_d1]
    rfl
  funext g
  change -(inducedCoordinates1 B W (canonicalCornerCochain W 1 _) g) =
    inducedCoordinates1 P W (canonicalPlaneCochain W 1 c) (BToP g) -
      inducedCoordinates1 Q W (canonicalLineCochain W 1 c) (BToQ g) -
      d₀₁ (Rep.res B.subtype W) (-inducedCoordinates0 B W (canonicalCornerCochain W 0 c)) g
  rw [canonicalCornerCochain_d1,map_add,map_neg,map_sub,inducedCoordinates_d0]
  have hl := inducedCoordinates_restrict1 B W Q fullB_le_Q (canonicalLineCochain W 1 c) g
  have hp := inducedCoordinates_restrict1 B W P fullB_le_P (canonicalPlaneCochain W 1 c) g
  change inducedCoordinates1 B W (canonicalLineArrow.f 1 ≫ canonicalLineCochain W 1 c) g =
    inducedCoordinates1 Q W (canonicalLineCochain W 1 c) (BToQ g) at hl
  change inducedCoordinates1 B W (canonicalPlaneArrow.f 1 ≫ canonicalPlaneCochain W 1 c) g =
    inducedCoordinates1 P W (canonicalPlaneCochain W 1 c) (BToP g) at hp
  change -(-d₀₁ (Rep.res B.subtype W) (inducedCoordinates0 B W (canonicalCornerCochain W 0 c)) g +
    (inducedCoordinates1 B W (canonicalLineArrow.f 1 ≫ canonicalLineCochain W 1 c) g -
     inducedCoordinates1 B W (canonicalPlaneArrow.f 1 ≫ canonicalPlaneCochain W 1 c) g)) = _
  rw [hl,hp,map_neg]
  change -(-_ + (_ - _)) = _ - _ - (-_)
  abel

/-- A literal isomorphism of three-term complexes, including every face and corner coefficient. -/
def ordinaryShortComplexIso : (canonicalCochains W).sc' 0 1 2 ≅ OrdinaryBoundaryCone.complex W P Q :=
  ShortComplex.isoMk (ordinaryCoordinates0 W).toModuleIso (ordinaryCoordinates1 W).toModuleIso
    (ordinaryCoordinates2 W).toModuleIso
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact (ordinaryCoordinates_d0 W c).symm)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      exact (ordinaryCoordinates_d1 W c).symm)

/-- Genuine canonical full-level boundary H1 is the ordinary algebraic P/Q/B cone H1. -/
def canonicalOrdinaryH1Iso : (canonicalCochains W).homology 1 ≅
    ModuleCat.of ℚ (OrdinaryBoundaryCone.H1 W P Q) :=
  (ShortComplex.homologyFunctor (ModuleCat ℚ)).mapIso
    ((canonicalCochains W).isoSc' 0 1 2 (by simp) (by simp) ≪≫ ordinaryShortComplexIso W) ≪≫
      OrdinaryBoundaryCone.homologyIso W P Q

end TernaryPoly.SymmetricSpaceBoundaryFull
