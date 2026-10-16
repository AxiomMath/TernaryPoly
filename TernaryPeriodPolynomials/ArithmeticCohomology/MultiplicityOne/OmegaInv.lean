module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.PairCharacterBound

@[expose] public section


/-!
# The Satake scalar of an inverse

The compression of `σ(g⁻¹)` to the `GL₂(ℤ̂^{(3)})`-fixed vectors is the adjoint of that of
`σ(g)` (`compression_star`), so `ω(B⁻¹) = conj ω(B)` for `B` trivial at three.
-/

noncomputable section

open ComplexConjugate
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.RepresentationTheory
open TernaryPeriodPolynomials.HeckeEigen.Satake

namespace TernaryPeriodPolynomials.MultiplicityOne

/-- **`ω(B⁻¹) = conj ω(B)`.** -/
theorem omega_inv (σ : CuspidalRepresentation) {B : BinaryFiniteGL}
    (hB : B ∈ awayGroup placeThree) : omega σ B⁻¹ = conj (omega σ B) := by
  rcases subsingleton_or_nontrivial (fixedVectors σ K3) with hs | hn
  · rw [Spectral.PairCharacterBound.omega_eq_zero_of_subsingleton σ B⁻¹,
      Spectral.PairCharacterBound.omega_eq_zero_of_subsingleton σ B, map_zero]
  · obtain ⟨w, hw⟩ := exists_ne (0 : fixedVectors σ K3)
    have hinv : atFinite B⁻¹ = (atFinite B)⁻¹ := map_inv atFiniteHom B
    have key : inner ℂ (compression σ K3 (atFinite B⁻¹) w) w =
        inner ℂ w (compression σ K3 (atFinite B) w) := by
      rw [hinv, ← compression_star, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    rw [omega_spec σ (inv_mem hB) w, omega_spec σ hB w, inner_smul_left, inner_smul_right] at key
    have hww : inner ℂ w w ≠ 0 := inner_self_ne_zero.mpr hw
    have hconj : conj (omega σ B⁻¹) = omega σ B := mul_right_cancel₀ hww key
    rw [← hconj, Complex.conj_conj]

end TernaryPeriodPolynomials.MultiplicityOne
