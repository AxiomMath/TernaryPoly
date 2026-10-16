module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SameConstituent
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SupportSphericity
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelOneParity
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.LocalThreeEntry
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Standard.GoodCusps

@[expose] public section


/-! The parent bad-plane detection statement, composed from the four proved
local/global inputs and the spherical detection child. -/

open GeneralEisenstein

namespace TernaryPeriodPolynomials

theorem eisenstein_bad_plane_detection (n : ℕ) (hn : 0 < n) (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hhol : PlaneEisensteinHolomorphic D)
    (T : boundarySummand D .plane →ₗ[ℂ] boundarySummand D .line)
    (hT : RealizesStandard D T) (ξ : boundarySummand D .plane)
    (hplane : VanishesOnGood n D.chi .plane ξ.val)
    (hline : VanishesOnGood n D.chi .line (T ξ).val) : ξ = 0 := by
  exact eisenstein_bad_plane_detection_of_pieces
    { representative :=
        TernaryPeriodPolynomials.BadPlaneSameConstituentRepresentative.bad_plane_same_constituent_representative
      sphericity := TernaryPeriodPolynomials.BadPlaneSupportSphericity.bad_plane_support_sphericity
      parity := TernaryPeriodPolynomials.LevelOneCohomologicalParity.level_one_cohomological_parity
      localEntry := TernaryPeriodPolynomials.LocalThreeBadPlaneEntry.local_three_bad_plane_entry
      globalDetection := spherical_standard_good_cusp_detection }
    n hn D hχ hhol T hT ξ hplane hline

end TernaryPeriodPolynomials
