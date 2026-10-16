module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.LiteralKappa

@[expose] public section


/-!
# Lemma B.1 (`lem:literal-residue-comparison`): literal Shapiro, Hochschild-Serre and edge maps

Formalized by Claude Sonnet 5.5.

**Statement (proved here, group homology only).**  With `G = GL₃(ℤ)`, `P_H` the stabilizer of `H = {a = 0}`,
`𝓡_n ⊗ det⁻¹` the residue module (the exponents `±1` of the determinant twist give the same `G`-module since `det = ±1`),
`D_{n+1} = Sym^{n+1}` with the untwisted integral `GL₂(ℤ)`-action:

* `shapiro_literal n : H₃(G, 𝓡_n ⊗ det⁻¹) ≃ₗ[ℚ] H₃(P_H, 𝓡_{n,H} ⊗ det⁻¹)` (Shapiro);
* `kappa_literal n : H₃(P_H, 𝓡_{n,H} ⊗ det⁻¹) ≃ₗ[ℚ] H₁(GL₂(ℤ), D_{n+1})` (Hochschild-Serre; the only total-degree-three term is
  `(1, 2)`; the determinant twist `det C` of the residue action and the inverse-conjugation factor `λ²/det C` on `H₂(ℤ²)`
  combine to `λ² = 1` on the integral Levi, `deltaG_eq`, `fiber_compat`);
* `residue_period_algebraic n : H₃(G, 𝓡_n ⊗ det⁻¹) ≃ₗ[ℚ] ℬ_{n+1}`: `edge₂ ∘ κ ∘ Sh` is an isomorphism onto the period space
  (the coefficient at the standard oriented edge of the dual Farey tree);
* `H3_G_duality n`: the unconditional Borel-Serre duality `H₃(G, 𝓡_n ⊗ det⁻¹) ≃ Hom_G(St, 𝓡_n ⊗ det⁻¹)`.

**Not proved (explicit interface).**  `ResidueComparisonSquare n` (= `PHCompat n`): `edge₂ ∘ κ ∘ Sh = c · res_H` for one fixed
`c ≠ 0`, with `res_H` the literal residue of the value on the identity apartment of the Borel-Serre dual.  This is the
remaining geometric content of the lemma (cellular model of the core `ℝ² × W₂ ⊂ W₃`, fibre integration, and the
apartment/top-cell bridge of Lemma 3.3); it is not an axiom and is not used by any proved statement.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.AppendixBLiteral

open TernaryPeriodPolynomials.Argument.AppendixBResidue TernaryPeriodPolynomials.Argument.FareyTree

/-- Shapiro for the residue module. -/
def shapiro_literal (n : ℕ) : groupHomology (ResRep n) 3 ≃ₗ[ℚ] groupHomology (FibRep n) 3 := shLit n

/-- The Hochschild-Serre isomorphism `κ`. -/
def kappa_literal (n : ℕ) : groupHomology (FibRep n) 3 ≃ₗ[ℚ] groupHomology (Dplain (n + 1)) 1 := kappaLit n

/-- `edge₂ ∘ κ ∘ Sh`: an isomorphism of `H₃(G, 𝓡_n ⊗ det⁻¹)` onto the period space. -/
def residue_period_algebraic (n : ℕ) :
    groupHomology (ResRep n) 3 ≃ₗ[ℚ] TernaryPoly.OrdinaryResiduePeriod.periodSpace (n + 1) :=
  residuePeriodAlg n

theorem residue_period_algebraic_bijective (n : ℕ) : Function.Bijective (residue_period_algebraic n) :=
  (residue_period_algebraic n).bijective

/-- The unconditional Borel-Serre duality for the residue module. -/
def H3_G_duality (n : ℕ) :
    groupHomology (ResRep n) 3 ≃ₗ[ℚ] TernaryPoly.OrdinaryFullCoefficient.ResidueHom n (-1) := H3_G_equiv n

/-- The comparison square of Lemma B.1. -/
abbrev ResidueComparisonSquare (n : ℕ) : Prop := PHCompat n

end TernaryPeriodPolynomials.Argument.Statements.AppendixBLiteral
