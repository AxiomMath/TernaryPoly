module

public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Vanishing
public import TernaryPeriodPolynomials.ArithmeticCohomology.TopVanishing.Transfer
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Isotropy
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.InvolutionLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Apolar

@[expose] public section


/-!
# Exactness of the twisted cup products from top-degree vanishing

`H⁴(Γ, ℂ) = 0` for the arithmetic level `Γ` in the homogeneous model follows from `H⁴ = 0` for
any finite-index subgroup, in particular from a free resolution of `ℂ` of length three over a
finite-index subgroup (the cellular chains of a three-dimensional acyclic complex with a free
action). It gives the exactness of the twisted cup products of global two-cocycles used for the
isotropy of the global boundary image.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous

namespace TernaryPeriodPolynomials.TopVanishing

open TernaryPeriodPolynomials.Duality

/-- The homogeneous-model vanishing for the level is `GlobalTopVanishing`. -/
theorem globalTopVanishing_of_topVanishing (h : IsTopVanishing rationalLevel) :
    GlobalTopVanishing := by
  intro f hf hcocycle
  obtain ⟨θ, hθ, hd⟩ := h f (fun γ x => hf γ x) hcocycle
  exact ⟨θ, fun γ x => hθ γ x, hd⟩

/-- `H⁴(Γ, ℂ) = 0` from a free resolution of length three over a finite-index subgroup. -/
theorem globalTopVanishing_of_freeResolution {Λ : Subgroup RationalGL3}
    (hle : Λ ≤ rationalLevel) (hindex : Λ.relIndex rationalLevel ≠ 0)
    (X : FreeResolution Λ 3) : GlobalTopVanishing :=
  globalTopVanishing_of_topVanishing
    (IsTopVanishing.of_le_of_relIndex hle hindex (topVanishing_of_freeResolution X))

/-- The plug-in for the isotropy argument: exactness of the twisted cup products of global
two-cocycles from `H⁴(Γ, ℂ) = 0` in the homogeneous model. -/
theorem cupProductExactness_of_topVanishing {n : ℕ} (D : InducingData n)
    (h : IsTopVanishing rationalLevel) : CupProductExactness D dualInvolution (dualPairing n) :=
  cupProductExactness_of_globalTopVanishing D dualInvolution
    (fun _ membership => dualInvolution_mem_rationalLevel membership) (dualPairing n)
    (fun g _ v w => dualPairing_invariant n D.chi g v w) (globalTopVanishing_of_topVanishing h)

/-- Exactness of the twisted cup products from a free resolution of length three over a
finite-index subgroup of the level. -/
theorem cupProductExactness_of_freeResolution {n : ℕ} (D : InducingData n)
    {Λ : Subgroup RationalGL3} (hle : Λ ≤ rationalLevel) (hindex : Λ.relIndex rationalLevel ≠ 0)
    (X : FreeResolution Λ 3) : CupProductExactness D dualInvolution (dualPairing n) :=
  cupProductExactness_of_topVanishing D
    (IsTopVanishing.of_le_of_relIndex hle hindex (topVanishing_of_freeResolution X))

end TernaryPeriodPolynomials.TopVanishing
