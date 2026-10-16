module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.PrimeHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.Assembly

@[expose] public section


/-!
# Hecke correspondences in group homology (Appendix B, "The Hecke transfer")

Formalized by Claude Sonnet 5.5.
Paper: ("A Hecke correspondence consists of
restriction, rational matrix transport, and transfer ... liftable residues are Hecke-stable"; `eq:Hecke-formula`
`T_3(p,1) = p T_2(p) + p^2 I`) and.

**Proved here (group homology only).**

* `transfer_corestriction`: transfer along a finite-index (not necessarily normal) subgroup `N ≤ K` followed by corestriction is
  multiplication by `[K : N]` (`trR_cor`); the transfer is natural in the coefficient module (`transfer_natural`);
* `hecke_image_stable`: for a Hecke datum `(ι, g, S, f)` and a morphism of `Ĝ`-modules `ψ : M → M'` the image of
  `H_n(Γ, M) → H_n(Γ, M')` is stable under the Hecke operator `cor_f ∘ g ∘ tr_S` (`range_heckeOp_stable`);
* `liftable_homology_hecke_stable`: the image of `H_3(GL₃(ℤ), singlePole) → H_3(GL₃(ℤ), 𝓡_n)` induced by the residue map is
  stable under the homology Hecke operator of `diag(p,1,1)⁻¹` (the first sentence of the proof, "liftable residues are
  Hecke-stable", at the level of group homology);
* `mackey_formula`: Mackey's double-coset formula `cor_P^Γ ≫ tr_S^Γ = ∑_x H_n(c_x) ∘ tr^P_{P ∩ x⁻¹Sx}` in group homology for
  arbitrary (non-normal) subgroups;
* `prime_hecke_decomposition`: the homology Hecke operator of `g = diag(p,1,1)⁻¹` on `H_k(GL₃(ℤ), 𝓡_n)` is, under the Shapiro
  isomorphism with `H_k(P_H, 𝓡_{n,H₀})`, the sum of the two `P_H`-level correspondences attached to the two double cosets
  `S_p · 1 · P_H` and `S_p · σ · P_H` of `S_p = {k | p ∣ k₀₁, p ∣ k₀₂}` in `GL₃(ℤ)` (`σ` the transposition `(0 1)`; the
  radical/Levi data `f₃ : (η,u,D) ↦ (η,pu,D)`, `f₁ : (η,u,D) ↦ (η, (u₀/p, u₁), (d₀₀, d₀₁/p; p d₁₀, d₁₁))`, `ξ₃ = diag(1/p,1,1)`,
  `ξ₁ = diag(1,1/p,1)`).

* `hecke_formula_literal` (added by S6; proved by S2 in `Proofs/HeckeHomology/Assembly.lean`): the evaluation of the two
  `P_H`-level correspondences under the Hochschild-Serre isomorphism `κ` (radical factors `p²` for the identity double coset,
  the `σ`-term for the other) and the resulting homology identity `T_3(p,1) = p T_2(p) + p² I`, on literal
  `H₃(GL₃(ℤ), 𝓡_n)`: `κ ∘ Sh ∘ T₃ = (p T₂(p) + p²) ∘ κ ∘ Sh` for every prime `p` and every `n`, with `T₂(p) = heckeOp (binDatum p)`
  the homology Hecke operator of `diag(1/p, 1)` on `H₁(GL₂(ℤ), Sym^{n+1})` (conventions: `Proofs/HeckeHomology/AssemblyConventions.lean`).
  The identification of this `T₂(p)` with the analytic Hecke operator on period polynomials is `Exports/HeckeBridge.lean`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.HeckeHomology

open TernaryPeriodPolynomials.Argument.HeckeHomology

alias transfer_corestriction := trR_cor
alias transfer_natural := trR_nat
alias hecke_image_stable := range_heckeOp_stable
alias liftable_homology_hecke_stable := liftableHomology_stable
alias mackey_formula := mackeyH
alias prime_hecke_decomposition := prime_hecke_pair
alias hecke_formula_literal := TernaryPeriodPolynomials.Argument.HeckeHomology.hecke_formula_literal
alias hecke2 := TernaryPeriodPolynomials.Argument.HeckeHomology.hecke2

end TernaryPeriodPolynomials.Argument.Statements.HeckeHomology
