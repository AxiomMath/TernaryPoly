module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.Tree.MapsUniformMain
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.AppendixBLiteral

@[expose] public section


/-!
# Lemma B.1 (`lem:literal-residue-comparison`), literal form

Formalized by Claude Sonnet 5.5.  The paper, Lemma B.1 and its proof.

**Statement.**  With `G = GL₃(ℤ)`, `P_H` the stabilizer of `H = {a = 0}`, `Sh : H₃(G, 𝓡_n ⊗ det) ≃ H₃(P_H, 𝓡_{n,H} ⊗ det)` (Shapiro),
`κ : H₃(P_H, 𝓡_{n,H} ⊗ det) ≃ H₁(GL₂(ℤ), D_{n+1})` (Hochschild-Serre for the radical `U ≅ ℤ²`), `edge₂` the coefficient of the standard
oriented binary well-rounded edge and `res_H` the literal residue at `a = 0` of the Borel-Serre dual:

* `lemma_B_1_literal`: there is ONE nonzero scalar `c`, independent of `n` and of the class, with `edge₂ (κ (Sh x)) = c • res_H x` for
  every `n` and every `x ∈ H₃(G, 𝓡_n ⊗ det)`; equality is in the same ambient space `ℚ[b, c]_{n+1}` of binary forms (no change of the
  variables; coefficientwise, so the comparison does not mix coefficients), and the composite is a linear isomorphism onto the space
  `ℬ_{n+1}` of symmetric separately odd period polynomials; `res_H` is bijective.
* Normalizations: with `resHLitNorm n := c • res_H` the square commutes exactly (`residuePeriodAlg_eq_resHLitNorm`); changing the
  orientation/averaging normalizations multiplies the comparison by a fixed nonzero scalar.

The scalar is `[G : Γ(6)] / ([P_H : P_N] c')` with `c' = c₂ / c₁`, `c₁ = -c₀ / |ker π|` (`c₀` the universal Schur scalar,
`TreeMapsUniform`), `c₂ = c_B · 2 / [P_H : P_N]` (`FidL_eq_coeff`).
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.LemmaB1Literal

open TernaryPeriodPolynomials.Argument.AppendixBResidue TernaryPoly
open TernaryPeriodPolynomials.Argument.GroupHomology

/-- The fixed nonzero scalar of the comparison square, independent of `n` and of the class. -/
def resScalar : ℚ := Classical.choose phCompatUniform_literal

theorem resScalar_ne_zero : resScalar ≠ 0 := (Classical.choose_spec phCompatUniform_literal).1

theorem residuePeriodAlg_eq_resScalar (n : ℕ) (x : groupHomology (ResRep n) 3) :
    residuePeriodAlg n x = resScalar • resHLit n x :=
  (Classical.choose_spec phCompatUniform_literal).2 n x

/-- The normalized literal residue `c • res_H`. -/
def resHLitNorm (n : ℕ) : groupHomology (ResRep n) 3 →ₗ[ℚ] OrdinaryResiduePeriod.periodSpace (n + 1) :=
  resScalar • resHLit n

/-- **The normalized diagram commutes exactly**: `edge₂ ∘ κ ∘ Sh = res_H^{norm}`. -/
theorem residuePeriodAlg_eq_resHLitNorm (n : ℕ) (x : groupHomology (ResRep n) 3) :
    residuePeriodAlg n x = resHLitNorm n x :=
  residuePeriodAlg_eq_resScalar n x

/-- The literal residue map `res_H` is bijective. -/
theorem resHLit_bijective (n : ℕ) : Function.Bijective (resHLit n) := by
  have hc := resScalar_ne_zero
  have hb := (residuePeriodAlg n).bijective
  have hf : ∀ x, resHLit n x = resScalar⁻¹ • residuePeriodAlg n x := fun x => by
    rw [residuePeriodAlg_eq_resScalar, smul_smul, inv_mul_cancel₀ hc, one_smul]
  constructor
  · intro x y h
    apply hb.1
    rw [residuePeriodAlg_eq_resScalar, residuePeriodAlg_eq_resScalar, h]
  · intro p
    obtain ⟨x, hx⟩ := hb.2 (resScalar • p)
    refine ⟨x, ?_⟩
    rw [hf, hx, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- The normalized residue is an isomorphism onto the period space. -/
theorem resHLitNorm_bijective (n : ℕ) : Function.Bijective (resHLitNorm n) := by
  have : (resHLitNorm n : groupHomology (ResRep n) 3 → _) = residuePeriodAlg n := by
    funext x
    exact (residuePeriodAlg_eq_resHLitNorm n x).symm
  rw [this]
  exact (residuePeriodAlg n).bijective

/-- **Lemma B.1, literal form.**  One fixed nonzero scalar `c` (independent of `n` and of the class) such that for every `n` and
every class `x`:

1. the square commutes up to `c`: `edge₂ (κ (Sh x)) = c • res_H x` in the period space;
2. the comparison is an equality of binary forms in the same variables `b, c` (no substitution), coefficientwise;
3. `edge₂ ∘ κ ∘ Sh` is a linear isomorphism onto the space of symmetric separately odd period polynomials, and `res_H` is bijective. -/
theorem lemma_B_1_literal :
    ∃ c : ℚ, c ≠ 0 ∧ ∀ n : ℕ,
      (∀ x : groupHomology (ResRep n) 3,
        Statements.BinaryDuality.periodEquivHomology' (n + 1)
            (Statements.AppendixBLiteral.kappa_literal n (Statements.AppendixBLiteral.shapiro_literal n x)) =
          c • resHLit n x) ∧
      (∀ x : groupHomology (ResRep n) 3,
        ((residuePeriodAlg n x : OrdinaryResiduePeriod.periodSpace (n + 1)) : MvPolynomial (Fin 2) ℚ) =
          c • ((resHLit n x : OrdinaryResiduePeriod.periodSpace (n + 1)) : MvPolynomial (Fin 2) ℚ)) ∧
      (∀ (x : groupHomology (ResRep n) 3) (m : Fin 2 →₀ ℕ),
        ((residuePeriodAlg n x : OrdinaryResiduePeriod.periodSpace (n + 1)) :
            MvPolynomial (Fin 2) ℚ).coeff m =
          c * ((resHLit n x : OrdinaryResiduePeriod.periodSpace (n + 1)) :
            MvPolynomial (Fin 2) ℚ).coeff m) ∧
      Function.Bijective (residuePeriodAlg n) ∧ Function.Bijective (resHLit n) := by
  refine ⟨resScalar, resScalar_ne_zero, fun n => ⟨fun x => residuePeriodAlg_eq_resScalar n x, fun x => ?_,
    fun x m => ?_, (residuePeriodAlg n).bijective, resHLit_bijective n⟩⟩
  · rw [residuePeriodAlg_eq_resScalar]
    rfl
  · rw [residuePeriodAlg_eq_resScalar]
    simp

end TernaryPeriodPolynomials.Argument.Statements.LemmaB1Literal
