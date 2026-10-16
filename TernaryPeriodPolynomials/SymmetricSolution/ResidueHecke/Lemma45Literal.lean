module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Literal.BinaryStabilityLiteral

@[expose] public section


/-!
# Lemma 4.5 (`lem:residue-period`) on literal group homology

Formalized by Claude Sonnet 5.5.
Paper: Lemma 4.5 and its proof.

> **Lemma 4.5.** The map sending `q ∈ ℬ_{n+1}` to the residue cycle represented by
> `F_q(a,b,c) = q(b,c)/a + q(a,c)/b + q(a,b)/c` identifies `ℬ_{n+1}` with `H₃(G, ℛ_n ⊗ det)`.  Its inverse reads the literal
> residue at `a = 0`, namely `q(b,c)`.  Let `𝓛_n` be the image of `H₃(G, ℳ_n ⊗ det)` in this space.  If `n > 0` then
> `[a c^n] q(a,c) = 0` for every `q ∈ 𝓛_n`.  Moreover `𝓛_n` is stable under the usual binary Hecke operators.

Here `H₃(G, -)` is Mathlib's `groupHomology (-) 3` for `G = GL₃(ℤ)`; `ℛ_n ⊗ det` is `ResRep n` and `ℳ_n ⊗ det` is `MRep n`;
`H3_G_equiv n` is the Steinberg functional of a class (Borel-Serre duality for the arithmetic group, built from the library's
cap-product duality); the literal residue `res_H = resHLit n` reads the coefficient of `1/a` of the value at the identity
apartment; `𝓛_n` is `LnHom n`, defined from homology and identified with the library's Hom-model `liftableResidueHoms`.

* `lemma_4_5_literal` bundles: (1) the unique class with literal residue `q`, whose functional takes the value `F_q` at the identity
  apartment; (2) the inverse reads `q(b,c)`; (3) `LnHom n` is the image of the Hom-model liftable residues; (4) the extreme
  coefficient `[a c^n]q = 0` (valid for every `n`, in particular `n > 0`); (5) stability under the homology Hecke operator `T₃(p,1)`
  and (6) under the binary operator `T₂(p)` on `ℬ_{n+1}` (the homology operator `heckeOp (binDatum p)` of `diag(1/p, 1)` on
  `H₁(GL₂(ℤ), Sym^{n+1})`, transported by the standard-edge isomorphism).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.Lemma45Literal

open TernaryPeriodPolynomials.Argument.Lemma45Literal TernaryPeriodPolynomials.Argument.AppendixBResidue
  TernaryPoly TernaryPoly.OrdinaryResiduePeriod

alias residue_cycle := Lemma45Literal.lemma_4_5_residue_cycle
alias residue_at_a_eq_zero := Lemma45Literal.residue_at_a_eq_zero
alias liftable_eq_hom_model := Lemma45Literal.LnHom_eq_liftable
alias extreme_coefficient := Lemma45Literal.LnHom_extreme_literal
alias hecke_stable_ternary := Lemma45Literal.LnHom_hecke_stable
alias hecke_stable_binary := Lemma45Literal.LnHom_binary_stable_literal

/-- **Lemma 4.5 on literal group homology** (sentences 1-3). -/
theorem lemma_4_5_literal (n : ℕ) :
    -- sentence 1: `q ↦ F_q` identifies `ℬ_{n+1}` with `H₃(G, ℛ_n ⊗ det)`
    (∀ q : periodSpace (n + 1), ∃! x : groupHomology (ResRep n) 3, resHLit n x = q ∧
      (H3_G_equiv n x).val (OrdinaryApartmentPresentation.frameCycle 1) = Lemma45Literal.Fq n q) ∧
    -- its inverse reads the literal residue at `a = 0`
    (∀ x : groupHomology (ResRep n) 3, ((resHLit n x).val : SinglePoleCoordinate.BinaryV (n + 1)) =
      SinglePoleCoordinate.literalFiberMap n 0
        ((H3_G_equiv n x).val (OrdinaryApartmentPresentation.frameCycle 1) (OrdinaryResidueSupport.axis 0))) ∧
    -- `𝓛_n` (from homology) is the image of the Hom-model liftable residues
    (Lemma45Literal.LnHom n = (OrdinaryFullCoefficient.liftableResidueHoms n (-1)).map (periodEquiv n).toLinearMap) ∧
    -- sentence 2: `[a c^n] q(a,c) = 0`
    (∀ q ∈ Lemma45Literal.LnHom n, (q.val : SinglePoleCoordinate.BinaryV (n + 1)).val.coeff (Finsupp.single 0 1 + Finsupp.single 1 n) = 0) ∧
    -- sentence 3: stability under `T₃(p,1)` and under the binary operator `T₂(p)`
    (∀ (p : ℕ) [Fact p.Prime], ∀ q ∈ Lemma45Literal.LnHom n, Lemma45Literal.T3B p n q ∈ Lemma45Literal.LnHom n) ∧
    (∀ (p : ℕ) [Fact p.Prime], ∀ q ∈ Lemma45Literal.LnHom n, Lemma45Literal.T2B p n q ∈ Lemma45Literal.LnHom n) :=
  ⟨Lemma45Literal.lemma_4_5_residue_cycle n, Lemma45Literal.residue_at_a_eq_zero n,
    Lemma45Literal.LnHom_eq_liftable n, Lemma45Literal.LnHom_extreme_literal n,
    fun p _ q hq => Lemma45Literal.LnHom_hecke_stable p n q hq,
    fun p _ q hq => Lemma45Literal.LnHom_binary_stable_literal p n q hq⟩

end TernaryPeriodPolynomials.Argument.Statements.Lemma45Literal
