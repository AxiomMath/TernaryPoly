module

public import TernaryPeriodPolynomials.Analysis.Scalar.EisensteinLevelThreeEichlerGeometry
public import TernaryPeriodPolynomials.ModularForm.Symbol.Coefficients
public import TernaryPeriodPolynomials.ModularForm.Eichler.Basic

@[expose] public section
noncomputable section
open Complex Matrix MatrixGroups
open UpperHalfPlane hiding I

namespace TernaryPoly.BinaryCuspSymbol
open BinaryCuspPeriod

/-- Actual determinant-one integral action in rational coordinates. -/
def slRational : SL2 →* GL2 := Matrix.SpecialLinearGroup.mapGL ℚ

/-- Actual full-level modularity for an arbitrary integral determinant-one matrix. -/
theorem cusp_slMobius {d : ℕ} (f : Forms d) (g : SL2) {z : ℂ} (hz : 0 < z.im) :
    f (ofComplex (slMobius g z)) = ((g 1 0 : ℂ)*z+(g 1 1 : ℂ))^(d+2) * f (ofComplex z) := by
  have hg : (g : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨g, rfl⟩
  have h := SlashInvariantForm.slash_action_eqn'' f hg (⟨z, hz⟩ : ℍ)
  have hp : (d : ℤ)+2 = ((d+2 : ℕ) : ℤ) := by omega
  simp only [hp, zpow_natCast, slDenom] at h
  rw [slMobius_eq_action g hz, ofComplex_apply, ofComplex_apply_of_im_pos hz]
  exact h

/-- Pullback of the actual period differential by any integral special-linear matrix. -/
theorem periodIntegrand_slMobius {d : ℕ} (f : Forms d) (g : SL2) (v : Coordinates)
    {z : ℂ} (hz : 0 < z.im) :
    periodIntegrand f (v 0) (v 1) (slMobius g z) *
      (1/((g 1 0 : ℂ)*z+(g 1 1 : ℂ))^2) =
        periodIntegrand f (slCoordinates g⁻¹ v 0) (slCoordinates g⁻¹ v 1) z := by
  rw [periodIntegrand, cusp_slMobius f g hz, slCoordinates_inv]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have hden := slDenom_ne_zero g hz
  have he : slMobius g z * v 1-v 0 =
      (z*(-(g 1 0 : ℂ)*v 0+(g 0 0 : ℂ)*v 1)-
        ((g 1 1 : ℂ)*v 0-(g 0 1 : ℂ)*v 1))/((g 1 0 : ℂ)*z+(g 1 1 : ℂ)) := by
    apply (eq_div_iff hden).2
    unfold slMobius
    rw [sub_mul, mul_right_comm (_ / _) (v 1) _, div_mul_cancel₀ _ hden]
    ring
  rw [he, div_pow, pow_add]
  unfold periodIntegrand
  field_simp [hden]

end TernaryPoly.BinaryCuspSymbol
