module

public import TernaryPeriodPolynomials.ModularForm.Endpoint.Shift

@[expose] public section


noncomputable section
open Complex MatrixGroups
open UpperHalfPlane hiding I

namespace TernaryPoly.BinaryCuspPeriod

/-- Literal full-level periodicity of the cusp form on its complex extension. -/
theorem cusp_translate_one {d : ℕ} (f : Forms d) (z : ℂ) :
    f (ofComplex (z+1)) = f (ofComplex z) :=
  SlashInvariantFormClass.periodic_comp_ofComplex f (by simp) z

/-- The S involution preserves the open upper half plane. -/
theorem neg_inv_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (-1/z).im := by
  simpa [neg_div, one_div, inv_neg] using (UpperHalfPlane.im_inv_neg_coe_pos ⟨z, hz⟩)

/-- Literal S-modularity, with the actual weight d+2 and no period-relation assumption. -/
theorem cusp_neg_inv {d : ℕ} (f : Forms d) {z : ℂ} (hz : 0 < z.im) :
    f (ofComplex (-1/z)) = z^(d+2) * f (ofComplex z) := by
  have hs : (ModularGroup.S : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨ModularGroup.S, rfl⟩
  have h := SlashInvariantForm.slash_action_eqn'' f hs (⟨z, hz⟩ : ℍ)
  have hp : (d : ℤ)+2 = ((d+2 : ℕ) : ℤ) := by omega
  change f (ModularGroup.S • (⟨z, hz⟩ : ℍ)) =
    (denom ModularGroup.S (⟨z, hz⟩ : ℍ))^((d : ℤ)+2) * f (⟨z, hz⟩ : ℍ) at h
  have hden : denom (ModularGroup.S : GL (Fin 2) ℝ) z = z :=
    ModularGroup.denom_S (z := (⟨z, hz⟩ : ℍ))
  simp only [hden, hp, zpow_natCast] at h
  have he : ofComplex (-1/z) = ModularGroup.S • (⟨z, hz⟩ : ℍ) := by
    rw [modular_S_smul, ofComplex_apply_of_im_pos (neg_inv_im_pos hz)]
    apply UpperHalfPlane.ext
    change -1/z = (-z)⁻¹
    simp [neg_div, one_div, inv_neg]
  rw [he, ofComplex_apply_of_im_pos hz]
  exact h

/-- T transforms the parameters of the actual period differential by (x,y)↦(x-y,y). -/
theorem periodIntegrand_translate {d : ℕ} (f : Forms d) (x y z : ℂ) :
    periodIntegrand f x y (z+1) = periodIntegrand f (x-y) y z := by
  unfold periodIntegrand
  rw [cusp_translate_one]
  congr 2
  ring

/-- The chain-rule differential for S has exactly the expected transformed parameters. -/
theorem periodIntegrand_neg_inv {d : ℕ} (hd : Even d) (f : Forms d)
    (x y : ℂ) {z : ℂ} (hz : 0 < z.im) :
    periodIntegrand f x y (-1/z) * (1/z^2) = periodIntegrand f (-y) x z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  unfold periodIntegrand
  rw [cusp_neg_inv f hz]
  have he : (-1/z)*y-x = -(z*x+y)/z := by field_simp; ring
  rw [he, div_pow, hd.neg_pow, pow_add]
  field_simp
  ring

end TernaryPoly.BinaryCuspPeriod
