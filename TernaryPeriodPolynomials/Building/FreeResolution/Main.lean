module

public import TernaryPeriodPolynomials.Building.FreeResolution.Exact
public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Main

@[expose] public section


/-!
# Top-degree vanishing for the arithmetic level

Original work by Claude Opus 5.5.

The augmented cellular chain complex of the well-rounded complex is a free resolution of `ℂ` of
length three over the principal congruence subgroup `Γ(3)`. Hence `H⁴(Γ(3), ℂ) = 0`, and by
transfer `H⁴(Γ, ℂ) = 0` for the arithmetic level `Γ`, which gives the exactness of the twisted
cup products of global two-cocycles.
-/

noncomputable section

namespace TernaryPeriodPolynomials.FreeResolution

open GeneralEisenstein TernaryPeriodPolynomials.TopVanishing
open TernaryPeriodPolynomials.Duality

/-- The well-rounded free resolution over `Γ(3)`. -/
def principalFreeResolution : FreeResolution principalLevel 3 := wellRounded.toFreeResolution

/-- `H⁴(Γ(3), ℂ) = 0` in the homogeneous model. -/
theorem topVanishing_principalLevel : IsTopVanishing principalLevel :=
  topVanishing_of_freeResolution principalFreeResolution

/-- `H⁴(Γ, ℂ) = 0` in the homogeneous model, for the arithmetic level `Γ`. -/
theorem topVanishing_rationalLevel : IsTopVanishing rationalLevel :=
  IsTopVanishing.of_le_of_relIndex principalLevel_le principalLevel_relIndex_ne_zero
    topVanishing_principalLevel

/-- Exactness of the twisted cup products of global two-cocycles. -/
theorem cupProductExactness {n : ℕ} (D : InducingData n) :
    CupProductExactness D dualInvolution (dualPairing n) :=
  cupProductExactness_of_topVanishing D topVanishing_rationalLevel

end TernaryPeriodPolynomials.FreeResolution
