module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.RadicalCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.PolynomialRestriction

@[expose] public section


/-!
# The restriction of the radical cocycle to the unipotent radical

For the radical cocycle `planeRadical` of the real plane parabolic, defined by the exact division
`x₂ · R(u) Q = ρ(u) (ι Q) - ι Q`, the restriction `x₂ = 0` of its value at a unipotent element
`u(s,t) = planeUnipotent s t` on a binary form `Q` is `-(s ∂₀ Q + t ∂₁ Q)`
(`binaryPolynomialRestrict_planeRadical_unipotent`).  This is the derivative form of the Kostant law
needed by `kostantLaw_of_derivative` (with `κ = -1` on the generators `u(1,0)`, `u(0,1)`).  The
proof is the first-order Taylor expansion of the unipotent substitution (`unip_taylor`):
`Q(x - (s,t) x₂) - Q(x) = -x₂ (s ∂₀ Q + t ∂₁ Q) + x₂² R`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

open MvPolynomial GeneralEisenstein
open GeneralEisenstein.Adelic (planeUnipotent)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (binaryPolynomialRestrict binaryPolynomialLift binaryPolynomialRestrict_pderiv
    binaryPolynomialRestrict_lift binaryPolynomialRestrict_X)

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

/-- The directional derivative `s ∂₀ + t ∂₁` on ternary polynomials. -/
def dirDeriv (s t : ℂ) (F : Poly) : Poly :=
  C s * pderiv (0 : Fin 3) F + C t * pderiv (1 : Fin 3) F

theorem dirDeriv_add (s t : ℂ) (F G : Poly) :
    dirDeriv s t (F + G) = dirDeriv s t F + dirDeriv s t G := by
  unfold dirDeriv
  rw [map_add, map_add]
  ring

theorem dirDeriv_mul (s t : ℂ) (F G : Poly) :
    dirDeriv s t (F * G) = dirDeriv s t F * G + F * dirDeriv s t G := by
  unfold dirDeriv
  rw [pderiv_mul, pderiv_mul]
  ring

theorem dirDeriv_C (s t a : ℂ) : dirDeriv s t (C a) = 0 := by
  unfold dirDeriv
  rw [pderiv_C, pderiv_C]
  ring

theorem dirDeriv_X (s t : ℂ) (i : Fin 3) : dirDeriv s t (X i) = ![C s, C t, 0] i := by
  fin_cases i <;> simp [dirDeriv, pderiv_X]

theorem substitute_unip_X (s t : ℂ) (i : Fin 3) :
    substitute ((planeUnipotent s t)⁻¹ : GL3) (X i) = X i - ![C s, C t, 0] i * X 2 := by
  fin_cases i
  · simpa using substitute_unip_X0 s t
  · simpa using substitute_unip_X1 s t
  · simpa using substitute_unip_X2 s t

/-- **First-order Taylor expansion of the unipotent substitution.** -/
theorem unip_taylor (s t : ℂ) (F : Poly) :
    ∃ R : Poly, substitute ((planeUnipotent s t)⁻¹ : GL3) F - F =
      (X 2 : Poly) * (-(dirDeriv s t F)) + (X 2 : Poly) ^ 2 * R := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, ?_⟩
    have h : substitute ((planeUnipotent s t)⁻¹ : GL3) (C a) = C a := by simp [substitute]
    rw [h, dirDeriv_C]
    ring
  | add p q hp hq =>
    obtain ⟨Rp, hp⟩ := hp
    obtain ⟨Rq, hq⟩ := hq
    refine ⟨Rp + Rq, ?_⟩
    rw [map_add, dirDeriv_add]
    linear_combination hp + hq
  | mul_X p i hp =>
    obtain ⟨Rp, hp⟩ := hp
    refine ⟨Rp * X i + ![C s, C t, 0] i * (dirDeriv s t p - X 2 * Rp), ?_⟩
    rw [map_mul, dirDeriv_mul, dirDeriv_X, substitute_unip_X]
    linear_combination (X i - ![C s, C t, 0] i * X 2) * hp

theorem binaryPolynomialRestrict_C (a : ℂ) : binaryPolynomialRestrict (C a) = C a := by
  simp [binaryPolynomialRestrict]

/-- **The derivative form of the Kostant law.**  The restriction `x₂ = 0` of the radical at a
unipotent element is `-(s ∂₀ Q + t ∂₁ Q)`. -/
theorem binaryPolynomialRestrict_planeRadical_unipotent (n : ℕ) (s t : ℝ)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    binaryPolynomialRestrict
        ((planeRadical n trivialCharacter ⟨planeUnipotent s t, planeUnipotent_mem s t⟩ Q :
          HomogeneousPoly n) : Poly) =
      -(C (algebraMap ℝ ℂ s) * pderiv (0 : Fin 2) (Q : Binary.Poly) +
        C (algebraMap ℝ ℂ t) * pderiv (1 : Fin 2) (Q : Binary.Poly)) := by
  obtain ⟨R, hR⟩ : ∃ R : Poly, ((planeRadical n trivialCharacter
      ⟨planeUnipotent s t, planeUnipotent_mem s t⟩ Q : HomogeneousPoly n) : Poly) = R := ⟨_, rfl⟩
  have h1 : (X 2 : Poly) * R = substitute
      ((planeUnipotent (algebraMap ℝ ℂ s) (algebraMap ℝ ℂ t))⁻¹ : GL3) (binaryEmbed (n + 1) Q) -
        binaryEmbed (n + 1) Q := by
    rw [← hR, X2_mul_planeRadical_unipotent, fullCoefficientComponent_planeUnipotent]
  obtain ⟨R2, h2⟩ := unip_taylor (algebraMap ℝ ℂ s) (algebraMap ℝ ℂ t) (binaryEmbed (n + 1) Q)
  have h3 : R = -(dirDeriv (algebraMap ℝ ℂ s) (algebraMap ℝ ℂ t) (binaryEmbed (n + 1) Q)) +
      (X 2 : Poly) * R2 := by
    apply mul_left_cancel₀ X2_ne_zero
    rw [h1, h2]
    ring
  have lift : binaryEmbed (n + 1) Q = binaryPolynomialLift (Q : Binary.Poly) := rfl
  have hres : binaryPolynomialRestrict (binaryEmbed (n + 1) Q) = (Q : Binary.Poly) := by
    rw [lift]
    exact binaryPolynomialRestrict_lift _
  have hd0 : binaryPolynomialRestrict (pderiv (0 : Fin 3) (binaryEmbed (n + 1) Q)) =
      pderiv (0 : Fin 2) (Q : Binary.Poly) := by
    have := binaryPolynomialRestrict_pderiv (0 : Fin 2) (binaryEmbed (n + 1) Q)
    rw [hres] at this
    exact this.symm
  have hd1 : binaryPolynomialRestrict (pderiv (1 : Fin 3) (binaryEmbed (n + 1) Q)) =
      pderiv (1 : Fin 2) (Q : Binary.Poly) := by
    have := binaryPolynomialRestrict_pderiv (1 : Fin 2) (binaryEmbed (n + 1) Q)
    rw [hres] at this
    exact this.symm
  have hD : binaryPolynomialRestrict
      (dirDeriv (algebraMap ℝ ℂ s) (algebraMap ℝ ℂ t) (binaryEmbed (n + 1) Q)) =
        C (algebraMap ℝ ℂ s) * pderiv (0 : Fin 2) (Q : Binary.Poly) +
          C (algebraMap ℝ ℂ t) * pderiv (1 : Fin 2) (Q : Binary.Poly) := by
    unfold dirDeriv
    rw [map_add, map_mul, map_mul, hd0, hd1, binaryPolynomialRestrict_C, binaryPolynomialRestrict_C]
  rw [hR, h3, map_add, map_mul, binaryPolynomialRestrict_X, map_neg, hD]
  simp

end TernaryPeriodPolynomials.SourceConstruction
