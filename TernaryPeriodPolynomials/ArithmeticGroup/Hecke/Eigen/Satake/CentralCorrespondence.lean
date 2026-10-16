module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.SphericalFixed

@[expose] public section


/-!
# The central Hecke correspondence `p · 1`

The scalar matrix `p · 1` is central, so its double coset under `rationalLevel` is a single coset
and `{p · 1}` is a complete set of representatives. For `p ≡ 1 (mod 3)` the correspondence is
away from three. This gives an actual `HeckeCorrespondence` to which the central eigenvalue
formula applies; for spherical data the formula then holds with no hypotheses.

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.RepresentationTheory

namespace TernaryPeriodPolynomials.HeckeEigen.Satake

variable {p : ℕ}

/-- The central correspondence with the single representative `p · 1`. -/
def pScalarCorr (hp : p.Prime) : HeckeCorrespondence where
  g := pScalar hp
  representatives := {pScalar hp}
  inDoubleCoset r hr := by
    rw [Finset.mem_singleton] at hr
    exact ⟨1, 1, by simp [hr]⟩
  complete a b := by
    refine ⟨pScalar hp, Finset.mem_singleton_self _, ?_⟩
    have : (pScalar hp)⁻¹ * (a.val * pScalar hp * b.val) = a.val * b.val := by
      rw [← pScalar_central hp a.val, mul_assoc, inv_mul_cancel_left]
    rw [this]
    exact rationalLevel.mul_mem a.property b.property
  disjoint r hr t ht _ := by
    rw [Finset.mem_singleton] at hr ht
    rw [hr, ht]

theorem pScalarCorr_g (hp : p.Prime) : (pScalarCorr hp).g = pScalar hp := rfl

theorem pScalar_entry (hp : p.Prime) (i j : Fin 3) :
    (pScalar hp).val i j = if i = j then (p : ℚ) else 0 := by
  rw [pScalar_val, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem pScalar_inv_entry (hp : p.Prime) (i j : Fin 3) :
    ((pScalar hp)⁻¹).val i j = if i = j then (p : ℚ)⁻¹ else 0 := by
  change ((p : ℚ)⁻¹ • (1 : Matrix (Fin 3) (Fin 3) ℚ)) i j = _
  rw [Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp

/-- **`p · 1` is away from three when `p ≡ 1 (mod 3)`.** -/
theorem pScalarCorr_awayThree (hp : p.Prime) (h1 : p % 3 = 1) : AwayThree (pScalarCorr hp) := by
  have hp3 : ((p : ℤ) : ZMod 3) ≠ 0 := by
    intro h
    have : (3 : ℤ) ∣ (p : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h
    omega
  refine ⟨fun i j => ⟨?_, ?_⟩, fun j => ?_⟩
  · rw [pScalarCorr_g, pScalar_entry]
    split_ifs
    · exact ⟨p, 1, by simp, by simp⟩
    · exact ⟨0, 1, by simp, by simp⟩
  · change IntegralAtThree (((pScalar hp)⁻¹).val i j)
    rw [pScalar_inv_entry]
    split_ifs
    · exact ⟨1, p, hp3, by simp⟩
    · exact ⟨0, 1, by simp, by simp⟩
  · rw [pScalarCorr_g, pScalar_entry]
    obtain ⟨k, hk⟩ : ∃ k : ℕ, p = 3 * k + 1 := ⟨p / 3, by omega⟩
    by_cases hj : (2 : Fin 3) = j
    · subst hj
      refine ⟨k, 1, by simp, ?_⟩
      simp only [ite_true, hk]
      push_cast
      ring
    · refine ⟨0, 1, by simp, ?_⟩
      have : j ≠ 2 := fun h => hj h.symm
      simp [hj, this]

/-- **Unconditional spherical central eigenvalue.** For spherical cusp data and a prime
`p ≡ 1 (mod 3)`, right translation of a plane induced section by the finite image of `p · 1`
multiplies it by `χ(sAd p) p^{-(n+3)} ω_σ(sAd p)`. -/
theorem central_translate_spherical {n : ℕ} (D : InducingData n) (hD : SphericalCusp D.cusp)
    (hp : p.Prime) (h1 : p % 3 = 1) (f : AdelicGL → ℂ)
    (hf : IsInduced D .plane cohomologicalPoint f) (g : AdelicGL) :
    f (g * atFinite (rationalFinite (pScalar hp))) =
      (D.chi.toMonoidHom (sAd (pUnit hp)) *
        (Complex.exp (-(((n : ℂ) + 3) * (Real.log p : ℂ))) *
          D.cusp.centralCharacter (sAd (pUnit hp)))) * f g := by
  have := fixedVectors_nontrivial_of_spherical D.cusp hD
  have h3 : p ≠ 3 := by omega
  have := central_plane_eigenvalue_cohomological D hp h3 (pScalarCorr hp)
    (pScalarCorr_awayThree hp h1) rfl (smooth_nonzero_of_spherical D.cusp hD) f hf g
  simpa [pScalarCorr] using this

end TernaryPeriodPolynomials.HeckeEigen.Satake
