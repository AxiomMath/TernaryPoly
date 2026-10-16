module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.BadPlane.SupportSphericity.Proof

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic

namespace TernaryPeriodPolynomials.BadPlaneSupportSphericity

theorem bad_plane_support_sphericity : ∀ n : ℕ, 0 < n → ∀ D : InducingData n, D.chi = trivialCharacter →
    ∀ ξ : boundarySummand D .plane, ξ ≠ 0 → BadPlaneRepresentative D ξ →
    SphericalCusp D.cusp := by
  intro degree _ data _ boundaryClass nonzero representative
  exact Helpers.spherical_of_supported_representative data boundaryClass nonzero representative

end TernaryPeriodPolynomials.BadPlaneSupportSphericity
