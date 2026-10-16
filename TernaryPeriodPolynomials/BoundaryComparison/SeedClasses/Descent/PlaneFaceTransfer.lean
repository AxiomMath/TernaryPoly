module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneFaceDescent
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Level.TransferBack

@[expose] public section


/-!
# Transfer back at a plane cusp: the level group's `𝒞_P(E)` is spanned by transfers of the `Γ(N)` classes

Paper: Lemma C.3 (`ar:lem:seed`).

`planeTransfer` is the transfer (corestriction) from Mathlib's `H²(Γ(N) ∩ h⁻¹Ph, E_n)` to the face
library's `H²(Γ_F, E_n)` of the stabilizer `Γ_F` of the plane `F = h⁻¹⟨e₁,e₂⟩` in the level group
(`LevelTransferBack.trLevel` composed with `planeH2Equiv.symm`).
`locallyInnerClasses_planeFlag_eq_transfer`: **a class is locally inner iff it is the transfer of a
class of `faceCuspidalInH2 N h n`** (the image of the literal mixed cuspidal group of the `Γ(N)` plane
group; by the unconditional Eichler--Shimura spanning it is the span of the seeds).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

variable (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (h : SL(3, ℤ)) (n : ℕ)
  (character : RankOneCharacter)

/-- **Transfer back at a plane cusp.**  The transfer of Mathlib's `H²(Γ(N) ∩ h⁻¹Ph, E_n)` to the
stabilizer `Γ_F` of the plane in the level group (read on the homogeneous side through `planeH2Equiv`). -/
def planeTransfer :
    groupCohomology.H2 (faceRep N h n) →ₗ[ℂ]
      GeneralEisenstein.Homogeneous.H2 (fixedPointLevel rationalLevel (planeFlagAt h))
        (rationalCoefficientComponent n character) :=
  (trLevel (rationalCoefficientComponent n character) (levelPrincipal N) (levelPrincipal_le N)
    (levelPrincipal_norm N) (planeFlagAt h)).comp
    (planeH2Equiv N h3 h n character hN).symm.toLinearMap

/-- **`𝒞(Γ_F) = tr(𝒞(Γ(N)))`.**  A class of the face library's `H²(Γ_F, E)` is locally inner iff it is the
transfer of an element of `faceCuspidalInH2 N h n`, the image of the mixed cuspidal group of the plane
group of `Γ(N)`. -/
theorem locallyInnerClasses_planeFlag_eq_transfer
    (x : GeneralEisenstein.Homogeneous.H2 (fixedPointLevel rationalLevel (planeFlagAt h))
      (rationalCoefficientComponent n character)) :
    x ∈ locallyInnerClasses n character .plane (planeFlagAt h) ↔
      ∃ y ∈ faceCuspidalInH2 N h n, planeTransfer N h3 hN h n character y = x := by
  constructor
  · intro hx
    refine ⟨planeH2Equiv N h3 h n character hN
        (resPrincipal N (planeFlagAt h) (rationalCoefficientComponent n character) x),
      (locallyInnerClasses_planeFlag_iff N h3 h n character hN x).mp hx, ?_⟩
    change trLevel (rationalCoefficientComponent n character) (levelPrincipal N)
      (levelPrincipal_le N) (levelPrincipal_norm N) (planeFlagAt h)
      ((planeH2Equiv N h3 h n character hN).symm (planeH2Equiv N h3 h n character hN _)) = x
    rw [LinearEquiv.symm_apply_apply]
    exact trLevel_resH2 _ _ _ _ _ x
  · rintro ⟨y, hy, rfl⟩
    rw [locallyInnerClasses_eq]
    have hy' : (planeH2Equiv N h3 h n character hN).symm y ∈
        locallyInnerAt (rationalCoefficientComponent n character) (levelPrincipal N)
          (planeFlagAt h) := by
      rw [mem_locallyInnerAt_iff_faceLocallyInner N h3 h n character hN,
        LinearEquiv.apply_symm_apply, ← faceCuspidalInH2_eq_locallyInner]
      exact hy
    exact trH2_mem_locallyInnerAt _ (levelPrincipal N) (levelPrincipal_le N)
      (levelPrincipal_norm N) (planeFlagAt h) _ hy'

end TernaryPeriodPolynomials.Argument.SeedC3S4c
