module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.DetectTwEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.Kostant
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.Radical

@[expose] public section


/-!
# The Kostant law for the radical cocycle of the odd character

Port of `SourceConstruction.DetectKostant`, `DetectRadical` and `DetectRadicalLaw` to a
rank-one character `χ` with `χ(-1_∞) = -1`.  The radical `planeRadical n χ` is defined for every
character, and on a unipotent element the character is trivial (`fullCoefficientComponent_planeUnipotent`
does not depend on `χ`), so the restriction `x₂ = 0` of `planeRadical n χ` at `u(s,t)` is
`-(s ∂₀ Q + t ∂₁ Q)` for every `χ` (`binaryPolynomialRestrict_planeRadical_unipotentTw`).  Hence a
radical cocycle `lam` agreeing on the radical lattice with `planeRadical n χ` satisfies the Kostant law
with `c = -1` (`kostantLawTw_of_planeRadical`).

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

open MvPolynomial GeneralEisenstein
open GeneralEisenstein.Adelic (planeUnipotent realAdeleUnit)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (RadicalLattice radicalLatticeFirst radicalLatticeSecond
    binaryHomogeneousRestrict binaryHomogeneousRestrict_apply binaryPolynomialRestrict
    binaryPolynomialRestrict_pderiv binaryPolynomialRestrict_lift binaryPolynomialRestrict_X
    binaryPolynomialLift)
open TernaryPeriodPolynomials.SourceConstruction

noncomputable section

namespace TernaryPeriodPolynomials.TwistedSource

/-- The Kostant law from the derivative form `res λ(u(e_i)) q = κ ∂_i q`. -/
theorem kostantLawTw_of_derivative {n : ℕ} {lam : RadicalLattice → (PlaneQ n →ₗ[ℂ] PlaneV n)} {κ : ℂ}
    (h0 : ∀ q : PlaneQ n,
      (binaryHomogeneousRestrict n (lam radicalLatticeFirst q)).val =
        κ • MvPolynomial.pderiv (0 : Fin 2) q.val)
    (h1 : ∀ q : PlaneQ n,
      (binaryHomogeneousRestrict n (lam radicalLatticeSecond q)).val =
        κ • MvPolynomial.pderiv (1 : Fin 2) q.val) :
    KostantLawTw n lam κ :=
  kostantLaw_of_derivative h0 h1

/-- **The derivative form of the Kostant law** for every character.  The restriction `x₂ = 0` of the
radical at a unipotent element is `-(s ∂₀ Q + t ∂₁ Q)`. -/
theorem binaryPolynomialRestrict_planeRadical_unipotentTw (n : ℕ) (χ : RankOneCharacter) (s t : ℝ)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    binaryPolynomialRestrict
        ((planeRadical n χ ⟨planeUnipotent s t, planeUnipotent_mem s t⟩ Q :
          HomogeneousPoly n) : Poly) =
      -(C (algebraMap ℝ ℂ s) * pderiv (0 : Fin 2) (Q : Binary.Poly) +
        C (algebraMap ℝ ℂ t) * pderiv (1 : Fin 2) (Q : Binary.Poly)) := by
  obtain ⟨R, hR⟩ : ∃ R : Poly, ((planeRadical n χ
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

/-- **The Kostant law for `planeRadical n χ`**, `c = -1`.  The hypothesis `hχ` is not needed (the
radical lattice is unipotent, where every character is trivial); it is carried to match the
signature of the rest of the odd-character chain. -/
theorem kostantLawTw_of_planeRadical (χ : RankOneCharacter)
    (_hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) {n : ℕ}
    {lam : RadicalLattice → (PlaneQ n →ₗ[ℂ] PlaneV n)}
    (hlam : ∀ (r : RadicalLattice) (q : PlaneQ n),
      lam r q =
        planeRadical n χ
          ⟨planeUnipotent (((r.toAdd.1 : ℤ) : ℝ)) (((r.toAdd.2 : ℤ) : ℝ)),
            planeUnipotent_mem _ _⟩ q) :
    KostantLawTw n lam (-1) := by
  apply kostantLawTw_of_derivative
  · intro q
    rw [hlam, binaryHomogeneousRestrict_apply,
      binaryPolynomialRestrict_planeRadical_unipotentTw]
    simp [radicalLatticeFirst]
  · intro q
    rw [hlam, binaryHomogeneousRestrict_apply,
      binaryPolynomialRestrict_planeRadical_unipotentTw]
    simp [radicalLatticeSecond]

end TernaryPeriodPolynomials.TwistedSource
