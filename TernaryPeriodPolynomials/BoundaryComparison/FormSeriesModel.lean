module

public import TernaryPeriodPolynomials.BoundaryComparison.SeriesModel.CochainReduction
public import TernaryPeriodPolynomials.BoundaryComparison.SeriesModel.ModelUnfolding
public import TernaryPeriodPolynomials.BoundaryComparison.SeriesModel.ChartAgreement
public import TernaryPeriodPolynomials.BoundaryComparison.SeriesModel.LinearStatement

@[expose] public section


/-!
# OB7 route A: the literal de Rham class of the form series versus the library's model Eisenstein class

Formalized by Claude Sonnet 5.5.
Paper: Appendix C.

**Proved (classical side, unconditional).**

* `bridge_gramCocycle_eisenstein` (Steps 1-2): the Gram-triangle cochain `F(y₀,y₁,y₂) = ∫_{[y_iy_iᵀ]} φ^*𝓔_P(ω_h)` on `GL₃(ℝ)`-vertices is a
  homogeneous `2`-cocycle of the model (`gramCocycle ∈ Homogeneous.cocycles (realLevel Γ) (realCoefficient n)`), and under
  `LevelTransfer.bridge` and `Γ ≅ realLevel Γ` its class is the `eisensteinClassC` (the complexified literal de Rham class).
* `coeff_gramCochain_tsum` (Step (b)): termwise integration over the Gram triangle (normal convergence on the compact image of the
  triangle, dominated by a summable family), coefficientwise sum over `Γ_P\Γ`.
* `summand_cone_chain`, `gTerm_eq_translated`, `coeff_gramCochain_translated` (Step (c), classical side): each term is `ρ(δ)⁻¹` of the seed pulled
  back to the Gram cone along the normalization, evaluated on the `δ`-translated triangle; hence the series cochain is
  `F(y) = ∑_{Γ_P δ ∈ Γ_P\Γ} ρ(δ)⁻¹ F_seed(δ y)`, the unfolded model sum.

* `ChartAgreement.lean` (R1a): `conePoint_apply_eq` (the first four plane coordinates of `conePoint` and `gramChart` agree on symmetric Gram matrices),
  `fderiv_conePoint_apply` (and their tangents), `seed_cone_eq_formPair` (the seed pulled back along `conePoint` is the library's `formPair`),
  `seedTri_translate`, `planeIntG_eq_seedTri`, **`coeff_gramCochain_planeIntG`**: `coeff_m F(y) = ∑'_{c} planeIntG n (f ∘ ofComplex) (realMat δ_c) (gramOf y_i) m`.
* `CochainLedger.lean` (R1b): `planeIntG_const_mul`, `planeIntG_planeHolData`, `cOmegaCoeff_eq` (the scalar ledger of the two halves of `cOmega`).
* `ModelUnfolding.lean`: `sectionEisensteinValue_apply`, `globalCocycle_coeff` (the model cocycle is the sum over rational plane flags of the source cocycle).
* `CochainReduction.lean`: `CochainTarget`, `eisensteinClassC_eq_of_cochainTarget`: a class identity (single `D`, single cusp, single scalar) reduces to an identity of cochain values at `(1, a, ab)`.

**Not proved, and not stated as a Lean interface.**  The paper's comparison between the form series and the model Eisenstein class is a
LINEAR identity for all cusp-indexed cusp-form inputs (including `0`), tied to the model source by a constructed seed/source dictionary.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.FormSeriesModel

open TernaryPeriodPolynomials.Argument.FormSeriesModel

alias bridge_gramCocycle_eisenstein := TernaryPeriodPolynomials.Argument.FormSeriesModel.bridge_gramCocycle_eisenstein
alias coeff_gramCochain_tsum := TernaryPeriodPolynomials.Argument.FormSeriesModel.coeff_gramCochain_tsum
alias coeff_gramCochain_translated := TernaryPeriodPolynomials.Argument.FormSeriesModel.coeff_gramCochain_translated
alias gTerm_eq_translated := TernaryPeriodPolynomials.Argument.FormSeriesModel.gTerm_eq_translated
alias summand_cone_chain := TernaryPeriodPolynomials.Argument.FormSeriesModel.summand_cone_chain
alias coeff_gramCochain_planeIntG := TernaryPeriodPolynomials.Argument.FormSeriesModel.coeff_gramCochain_planeIntG
alias cOmegaCoeff_eq := TernaryPeriodPolynomials.Argument.FormSeriesModel.cOmegaCoeff_eq
alias globalCocycle_coeff := TernaryPeriodPolynomials.Argument.FormSeriesModel.globalCocycle_coeff
alias eisensteinClassC_eq_of_cochainTarget := TernaryPeriodPolynomials.Argument.FormSeriesModel.eisensteinClassC_eq_of_cochainTarget
alias seed_cone_eq_formPair := TernaryPeriodPolynomials.Argument.FormSeriesModel.seed_cone_eq_formPair
alias modelClassK := TernaryPeriodPolynomials.Argument.FormSeriesModel.modelClassK
alias FormSeriesEqModelLinear := TernaryPeriodPolynomials.Argument.FormSeriesModel.FormSeriesEqModelLinear

end TernaryPeriodPolynomials.Argument.Statements.FormSeriesModel
