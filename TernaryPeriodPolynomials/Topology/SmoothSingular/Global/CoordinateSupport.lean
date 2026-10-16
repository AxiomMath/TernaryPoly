module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CoordinateRestriction
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ScalarSupportDiagrams
public import TernaryPeriodPolynomials.Topology.SingularLocal.Support.Cochains

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits Set SymmetricSpaceCovering
open SingularLocalSupport EquivariantSingularSmall
variable (A : Rep.{0} ℚ DeckGroup)

/-- Actual rational coordinate support kernels agree with the fiber-valued local support kernels. -/
def coordinateSupportLocalIso (K : Set OrbitSpace) :
    rationalCoverSupport A K ≅ supportCochains (coverProjection univ) A K :=
  kernel.mapIso _ _ (rationalCoverGlobalLocalIso A) (rationalCoverLocalIso A Kᶜ)
    (rationalCoverLocalIso_restriction A Kᶜ)

/-- The actual support comparison retains the literal ambient comparison map. -/
theorem coordinateSupportLocalIso_forget (K : Set OrbitSpace) :
    (coordinateSupportLocalIso A K).hom ≫ supportInclusion (coverProjection univ) A K =
      kernel.ι (rationalCoverRestriction A (subset_univ Kᶜ)) ≫ (rationalCoverGlobalLocalIso A).hom :=
  kernel.lift_ι _ _ _

/-- The actual coordinate/local support comparison commutes with every support enlargement. -/
theorem coordinateSupportLocalIso_natural (K L : Set OrbitSpace) (hKL : K ⊆ L) :
    rationalCoverSupportMap A K L hKL ≫ (coordinateSupportLocalIso A L).hom =
      (coordinateSupportLocalIso A K).hom ≫ supportMap (coverProjection univ) A K L hKL :=
  supportSquare_of_mono
    (kernel.ι (rationalCoverRestriction A (subset_univ Kᶜ)))
    (kernel.ι (rationalCoverRestriction A (subset_univ Lᶜ)))
    (supportInclusion (coverProjection univ) A K) (supportInclusion (coverProjection univ) A L)
    (rationalCoverSupportMap A K L hKL) (supportMap (coverProjection univ) A K L hKL)
    (coordinateSupportLocalIso A K).hom (coordinateSupportLocalIso A L).hom
    (rationalCoverGlobalLocalIso A).hom (rationalCoverSupportMap_forget A K L hKL)
    (supportMap_inclusion (coverProjection univ) A K L hKL)
    (coordinateSupportLocalIso_forget A K) (coordinateSupportLocalIso_forget A L)

end TernaryPoly.SmoothSingularGlobal
