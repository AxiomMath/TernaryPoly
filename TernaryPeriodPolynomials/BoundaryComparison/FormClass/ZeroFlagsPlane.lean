module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.PropC5GammaN

@[expose] public section


/-!
# Mixed cuspidal plane restrictions force zero flag restrictions

Formalized by Claude Sonnet 5.5.
`zeroFlags_of_plane_mixed`: the plane counterpart of the `zeroFlags_of_line_mixed` (the flag group `Γ(N) ∩ g⁻¹Bg` is the stabilizer of the standard flag over the plane `g⁻¹Pg`).
-/

open scoped MatrixGroups DirectSum
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (n : ℕ)

/-- **Mixed cuspidal plane restrictions force zero flag restrictions** (the plane counterpart of S1's `zeroFlags_of_line_mixed`): the flag group
`Γ(N) ∩ g⁻¹Bg` is the stabilizer of the standard flag over the plane `g⁻¹Pg`, on which every locally inner class vanishes. -/
theorem zeroFlags_of_plane_mixed (hN : 3 ≤ N) (c : groupCohomology.H2 (gammaNRepAll N n))
    (hm : ∀ h : SL(3, ℤ), rPlane N n h c ∈ faceCuspidalInH2 N h n) : ZeroFlags N n c := by
  intro g
  have h1 := hm g
  rw [faceCuspidalInH2_eq_locallyInner, faceLocallyInner_eq_iInf] at h1
  have h2 := LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp h1 1)
  have himg := faceFlagStab_one_map N hN g
  let e : faceFlagStab N g 1 ≃* (faceFlagStab N g 1).map (gammaNPAt N g).subtype :=
    Subgroup.equivMapOfInjective _ _ (gammaNPAt N g).subtype_injective
  let e2 : (faceFlagStab N g 1).map (gammaNPAt N g).subtype ≃* gammaNBAt N g := MulEquiv.subgroupCongr himg
  let κ : gammaNBAt N g →* faceFlagStab N g 1 := (e.trans e2).symm.toMonoidHom
  exact res_eq_zero_of_res_res (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN N g hp))
    (faceFlagStab N g 1).subtype (Subgroup.inclusion (gammaNBAt_le_gammaN N g)) κ
    (MonoidHom.ext fun b => by
      apply Subtype.ext
      change (b : SL(3, ℤ)) = (((e.trans e2).symm b : faceFlagStab N g 1) : SL(3, ℤ))
      have := (e.trans e2).apply_symm_apply b
      exact (congrArg (fun x : gammaNBAt N g => (x : SL(3, ℤ))) this).symm)
    (gammaNRepAll N n) c h2

end TernaryPeriodPolynomials.Argument.FormClassK
