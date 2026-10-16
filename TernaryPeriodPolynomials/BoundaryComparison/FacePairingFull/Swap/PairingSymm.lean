module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.InvolutionLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Apolar

@[expose] public section


/-!
# The coefficient pairing `dualPairing` is symmetric

The apolar pairing `⟨f, k⟩ = ∑ₘ (∏ᵢ mᵢ!) fₘ kₘ` is symmetric (`apolarPoly_comm`), and twisting one slot
by the diagonal matrix `a = diag(1, 1, 3)` (symmetric) keeps it so: `dualPairing n v w = dualPairing n w v`
(`dualPairing_comm`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein MvPolynomial Matrix TernaryPeriodPolynomials.Duality

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Swap

theorem apolarPoly_comm (f k : Poly) : apolarPoly f k = apolarPoly k f := by
  induction f using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [apolarPoly_monomial, apolarPoly_monomial_right]
    ring
  | add p q hp hq => rw [map_add, LinearMap.add_apply, hp, hq, map_add]

theorem dualPairing_comm (n : ℕ) (v w : HomogeneousPoly n) :
    dualPairing n v w = dualPairing n w v := by
  rw [dualPairing_apply, dualPairing_apply, apolar_apply, apolar_apply, homogeneousSubstitute_coe,
    homogeneousSubstitute_coe]
  have hB : complexLevelScale ᵀ = complexLevelScale := by
    rw [complexLevelScale_eq, Matrix.diagonal_transpose]
  have h := apolarPoly_substitute ((complexify levelScale)⁻¹ : GL3).val complexLevelScale
    (by rw [hB]; exact (complexify levelScale).inv_mul) (substitute complexLevelScale (v : Poly))
    (w : Poly)
  have h2 : substitute ((complexify levelScale)⁻¹ : GL3).val (substitute complexLevelScale (v : Poly))
      = (v : Poly) := by
    rw [← AlgHom.comp_apply, substitute_comp]
    have : complexLevelScale * ((complexify levelScale)⁻¹ : GL3).val = 1 :=
      (complexify levelScale).mul_inv
    rw [this, substitute_one, AlgHom.id_apply]
  rw [h2] at h
  rw [h, apolarPoly_comm]

end TernaryPeriodPolynomials.Argument.FacePairingFull.Swap
