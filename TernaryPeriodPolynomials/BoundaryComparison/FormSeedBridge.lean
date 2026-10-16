module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.SeedGram
public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.Reflected
public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.LevelOneFree
public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.ReflectedClass
public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.AntiHolomorphic
public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.OtherCusps

@[expose] public section


/-!
# G5, holomorphic half at `Γ_P = Γ(N) ∩ P(ℤ)`: the model's plane integral cochain versus the seed class of Lemma C.3

Formalized by Claude Sonnet 5.5.  The paper, Lemma C.3 (`ar:lem:seed`), and the Eisenstein class at the
plane cusp.

**Proved.**
* `coneFaceEquiv`: the first four plane coordinates of the unimodular normalization give an equivariant map Gram cone `→ e(P)` for `Γ_P`
  (`planeAct_plm_pr4`: translations do not involve the fifth coordinate, the Levi part has `t = 1`).
* `bridge_gramCocycleW_seed`: for every holomorphic `h` with the Levi modularity of `Γ_P` and moment primitives (the hypotheses of the seed class),
  the Gram-triangle cocycle of the pulled-back seed `ω_h` on `GL₃(ℝ)`-vertices has, under `LevelTransfer.bridge`, the class
  `complexifyG N n (seedClass …)` (`bridge_pullback` + `deRhamClass_seedInv`).
* `coeff_gramCochainW_seed`, `planeIntG_one`: its coefficients are the library's `planeIntG n h 1`.
* `cOmegaCoeff_one_eq`: the level-one scalar ledger `cOmegaCoeff n D F y 1 κ = K · (coeff of the seed cocycle + J-reflected half)`,
  `K = (-1)ⁿ (n+1) c_F(1)/2`, `H = F(1 · b_F(1))`.
* `planeIntG_eq_seedTri_gl`: the reflected half is the `ρ(ε)⁻¹`-twisted seed cochain at the vertices `ε y_i`.

* R1c (`Reflected.lean`): `reflCocycle`, `coeff_reflCocycle`, `cOmegaCoeff_one_eq_cocycle`, `bridge_reflCocycle` and **`g5_levelOne`**: the model's `cOmega` at the identity plane
  is `K · (c_H + ε-transport of c_{H'})`, and its class is `[seed H] + ε_*[seed H']` (`ε_*` = conjugation by `ε = diag(-1,1,1)` with coefficient map `ρ(ε)`).

* Item (3) (`Modularity.lean`, `Holomorphy.lean`, `LevelOneFree.lean`): holomorphy of the scalar `F(x)` at every adelic base (`scalar_holomorphic_allBases`), Levi modularity of `H = F(1·b_F(1))`
  and `H' = F(J·b_F(1))` for `Γ_P = Γ(N) ∩ P(ℤ)`, `3 ∣ N` (`hmod_H`, `hmod_H'`, via the base-general `cuspScalarWeightedRealization_modular_base`, `bFin_one_integral`, `conjJ`) and the moment primitives
  (`exists_moment_primitives`).  **`g5_levelOne_of_eichler`**: for an `EichlerInput I` of the inducing datum and `F = cuspScalarWeightedRealization D.cusp I.halfWeight I.vector`, `g5_levelOne` holds with NO hypotheses on `H, H'`.

**Not proved.**  (The hypotheses on the
scalar function (holomorphy, Levi modularity, moment primitives) from an adelic datum, and the general-`Γ(N)` clause (adelic realization of
`CuspForm (leviGroup N)`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.FormSeedBridge

open TernaryPeriodPolynomials.Argument

alias planeAct_plm_pr4 := TernaryPeriodPolynomials.Argument.FormSeedBridge.planeAct_plm_pr4
alias coneFaceEquiv := TernaryPeriodPolynomials.Argument.FormSeedBridge.coneFaceEquiv
alias seedCone := TernaryPeriodPolynomials.Argument.FormSeedBridge.seedCone
alias seedCone_pair := TernaryPeriodPolynomials.Argument.FormSeedBridge.seedCone_pair
alias coeff_gramCochainW_seed := TernaryPeriodPolynomials.Argument.FormSeedBridge.coeff_gramCochainW_seed
alias planeIntG_one := TernaryPeriodPolynomials.Argument.FormSeedBridge.planeIntG_one
alias bridge_gramCocycleW_seed := TernaryPeriodPolynomials.Argument.FormSeedBridge.bridge_gramCocycleW_seed
alias cOmegaCoeff_one_eq := TernaryPeriodPolynomials.Argument.FormSeedBridge.cOmegaCoeff_one_eq
alias planeIntG_eq_seedTri_gl := TernaryPeriodPolynomials.Argument.FormSeedBridge.planeIntG_eq_seedTri_gl
alias coeff_reflCocycle := TernaryPeriodPolynomials.Argument.FormSeedBridge.coeff_reflCocycle
alias cOmegaCoeff_one_eq_cocycle := TernaryPeriodPolynomials.Argument.FormSeedBridge.cOmegaCoeff_one_eq_cocycle
alias bridge_reflCocycle := TernaryPeriodPolynomials.Argument.FormSeedBridge.bridge_reflCocycle
alias g5_levelOne := TernaryPeriodPolynomials.Argument.FormSeedBridge.g5_levelOne
alias scalar_holomorphic_allBases := TernaryPeriodPolynomials.Argument.FormSeedBridge.scalar_holomorphic_allBases
alias hmod_H := TernaryPeriodPolynomials.Argument.FormSeedBridge.hmod_H
alias hmod_H' := TernaryPeriodPolynomials.Argument.FormSeedBridge.hmod_H'
alias bFin_one_integral := TernaryPeriodPolynomials.Argument.FormSeedBridge.bFin_one_integral
alias SeedHyp := TernaryPeriodPolynomials.Argument.FormSeedBridge.SeedHyp
alias LevelOneConclusion := TernaryPeriodPolynomials.Argument.FormSeedBridge.LevelOneConclusion
alias g5_levelOne_of_eichler := TernaryPeriodPolynomials.Argument.FormSeedBridge.g5_levelOne_of_eichler
alias reflEquivMap := TernaryPeriodPolynomials.Argument.FormSeedBridge.reflEquivMap
alias reflected_form_eq := TernaryPeriodPolynomials.Argument.FormSeedBridge.reflected_form_eq
alias complexifyG_eps_map := TernaryPeriodPolynomials.Argument.FormSeedBridge.complexifyG_eps_map
alias eps_seedClass := TernaryPeriodPolynomials.Argument.FormSeedBridge.eps_seedClass
alias mob_eps := TernaryPeriodPolynomials.Argument.FormSeedBridge.mob_eps
alias dnm_eps := TernaryPeriodPolynomials.Argument.FormSeedBridge.dnm_eps
alias hStar_differentiableOn := TernaryPeriodPolynomials.Argument.FormSeedBridge.hStar_differentiableOn
alias hStar_hmod := TernaryPeriodPolynomials.Argument.FormSeedBridge.hStar_hmod
alias g5_levelOne_antiholomorphic := TernaryPeriodPolynomials.Argument.FormSeedBridge.g5_levelOne_antiholomorphic
alias cuspCocycle := TernaryPeriodPolynomials.Argument.FormSeedBridge.cuspCocycle
alias class_transport_cusp := TernaryPeriodPolynomials.Argument.FormSeedBridge.class_transport_cusp
alias cOmegaCoeff_eq_cocycle := TernaryPeriodPolynomials.Argument.FormSeedBridge.cOmegaCoeff_eq_cocycle
alias bFin_integral := TernaryPeriodPolynomials.Argument.FormSeedBridge.bFin_integral
alias bF_rational_integral := TernaryPeriodPolynomials.Argument.FormSeedBridge.bF_rational_integral
alias hmod_H_of_bF := TernaryPeriodPolynomials.Argument.FormSeedBridge.hmod_H_of_bF
alias hmod_H'_of_bF := TernaryPeriodPolynomials.Argument.FormSeedBridge.hmod_H'_of_bF
alias g5_levelOne_cusp := TernaryPeriodPolynomials.Argument.FormSeedBridge.g5_levelOne_cusp

end TernaryPeriodPolynomials.Argument.Statements.FormSeedBridge
