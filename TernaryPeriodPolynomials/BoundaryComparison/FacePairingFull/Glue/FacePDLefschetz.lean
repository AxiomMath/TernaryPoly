module

public import Mathlib

@[expose] public section


/-!
# Pairing between the images of compactly supported cohomology (Poincare-Lefschetz)

Formalized by Claude Sonnet 5.5.

The abstract algebra of this argument.  Let `j : H_c(E) → H(E)` and `j' : H_c(E*) → H(E*)` be the maps from compactly supported
to ordinary cohomology, `PD : H_c(E) × H(E*) → ℂ` and `PD' : H(E) × H_c(E*) → ℂ` the Poincare-Lefschetz pairings, assumed
nondegenerate on the side used, and `PD a (j' b) = PD' (j a) b` ("`j'` is the transpose of `j`").  Then
`⟨j a, j' b⟩ := PD a (j' b) = PD' (j a) b` is a well-defined pairing between the images `Im j × Im j'`
(`imagePairing`), nondegenerate in both arguments (`imagePairing_left_nondegenerate`, `imagePairing_right_nondegenerate`).
No finite-dimensionality is needed.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD

namespace Lefschetz

variable {Hc Hc' H H' : Type*} [AddCommGroup Hc] [Module ℂ Hc] [AddCommGroup Hc'] [Module ℂ Hc']
  [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H']
  (PD : Hc →ₗ[ℂ] H' →ₗ[ℂ] ℂ) (PD' : H →ₗ[ℂ] Hc' →ₗ[ℂ] ℂ) (j : Hc →ₗ[ℂ] H) (j' : Hc' →ₗ[ℂ] H')

/-- The restriction of `PD` to the image of `j'` factors through `H_c / ker j ≅ Im j` when `j'` is the transpose of `j`. -/
def imagePairing (hT : ∀ a b, PD a (j' b) = PD' (j a) b) :
    LinearMap.range j →ₗ[ℂ] LinearMap.range j' →ₗ[ℂ] ℂ :=
  ((LinearMap.ker j).liftQ (PD.compl₂ (LinearMap.range j').subtype) (by
    intro a ha
    apply LinearMap.ext
    rintro ⟨y, b, rfl⟩
    have : j a = 0 := ha
    change PD a (j' b) = 0
    rw [hT, this]
    simp)).comp (LinearMap.quotKerEquivRange j).symm.toLinearMap

theorem imagePairing_apply (hT : ∀ a b, PD a (j' b) = PD' (j a) b) (a : Hc) (b : Hc') :
    imagePairing PD PD' j j' hT ⟨j a, a, rfl⟩ ⟨j' b, b, rfl⟩ = PD a (j' b) := by
  have h : (LinearMap.quotKerEquivRange j).symm ⟨j a, a, rfl⟩ = Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp only [imagePairing, LinearMap.comp_apply, LinearEquiv.coe_coe, h]
  rfl

/-- **Left nondegeneracy** of the pairing between the images: the annihilator of `Im j'` in `Im j` is zero, because it lies
in the kernel of `PD'` (`PD' (j a) b = PD a (j' b)`). -/
theorem imagePairing_left_nondegenerate (hT : ∀ a b, PD a (j' b) = PD' (j a) b)
    (hPD' : ∀ x : H, (∀ b, PD' x b = 0) → x = 0) (x : LinearMap.range j)
    (h : ∀ y : LinearMap.range j', imagePairing PD PD' j j' hT x y = 0) : x = 0 := by
  obtain ⟨_, a, rfl⟩ := x
  have : j a = 0 := hPD' _ (fun b => by
    rw [← hT]
    exact by simpa [imagePairing_apply] using h ⟨j' b, b, rfl⟩)
  exact Subtype.ext this

/-- **Right nondegeneracy**: the annihilator of `Im j` in `Im j'` is zero, because it lies in the kernel of `PD`. -/
theorem imagePairing_right_nondegenerate (hT : ∀ a b, PD a (j' b) = PD' (j a) b)
    (hPD : ∀ y : H', (∀ a, PD a y = 0) → y = 0) (y : LinearMap.range j')
    (h : ∀ x : LinearMap.range j, imagePairing PD PD' j j' hT x y = 0) : y = 0 := by
  obtain ⟨_, b, rfl⟩ := y
  have : j' b = 0 := hPD _ (fun a => by simpa [imagePairing_apply] using h ⟨j a, a, rfl⟩)
  exact Subtype.ext this

end Lefschetz

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue.FacePD

end
