module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.ReflSeed
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.LineClass
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.ClassFinal
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.LineClassPaper
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage.Final
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Passage

@[expose] public section


/-!
# The geometric line seed (CMP-8, line half; core exports)

Aliases for the geometric core of the line mirror of `LiteralExports/SeedC3` (`Revision/Proofs/LineSeed/`).

**What is literal.**  The seed is the form of the paper's line section,
`σ_h = h(τ)(τZ - Y)ⁿ (τ dw₁ + dw₂) ∧ dτ` on the line face `{(w₁, w₂, x, y) : y > 0}`, `τ = x + iy`
(`TernaryPeriodPolynomials.Argument.Statements.RealEntryNormalization.lineSeedForm`): `line_psi_poly`, `line_eta_form`
(the primitive `η = h(τ)(τw₁ + w₂)(τZ - Y)ⁿ dτ` of `Proofs/LineSeed/LineEta`) and `to_poly_d_line_eta_form` (`dη = σ_h` as the
coefficient polynomial of `lineSeedForm`).  The class `seed_class` is the class in `H²(G, E_n)` of the zig-zag datum `(η, θ_g)`
(`seed_datum`, `θ_g = theta_form`, `dθ_g = g^*η - ρ(g)η` by `d_theta_eq`), i.e. the Čech--de Rham class of the closed
`ρ`-equivariant form `σ_h` (`seed_inv`, `de_rham_class_seed_inv`); `to_poly_cochain` is the closed form of its cocycle.
`refl_seed_inv` is the reflection-isotypic form `σ_f + ε(-1)ⁿ \overline{σ_{f^*}}` (sign `(-1)ⁿ`, `pull_form_lrefl_refl_seed`).
Nothing here is a model: `G` is any group with a determinant-one Levi block `lam` and a radical vector `v` (`LineData`), acting on the
face by `(w, τ) ↦ ((w + v)C⁻¹, Cτ)` and on `E_n = Sym^n((ℂ³)*) ⊗ det⁻¹` through `[[1, v], [0, lam]]`.

Formalized by Claude Sonnet 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.LineSeed

open TernaryPeriodPolynomials.Argument.LineSeed

alias LineData := TernaryPeriodPolynomials.Argument.LineSeed.LineData
alias line_data_act := LineData.act
alias line_data_action := LineData.action
alias line_data_act_mul := LineData.act_mul
alias line_data_rho_r := LineData.rhoR
alias line_rho_lmat_p_poly := rho_lmat_Ppoly
alias line_psi_poly := linePsiPoly
alias line_psi_val := linePsiVal
alias to_poly_line_psi_val := toPoly_linePsiVal
alias line_eta_form := lineEtaForm
alias to_poly_d_line_eta_form := toPoly_d_lineEtaForm
alias line_defect_poly := LineData.defect_poly
alias theta_fun := LineData.thetaFun
alias to_poly_theta_fun := LineData.toPoly_thetaFun
alias theta_form := LineData.thetaForm
alias d_theta_eq := LineData.dTheta_eq
alias seed_datum := LineData.seedDatum
alias seed_inv := LineData.seedInv
alias seed_class := LineData.seedClass
alias de_rham_class_seed_inv := LineData.deRhamClass_seedInv
alias to_poly_cochain := LineData.toPoly_cochain
alias line_refl_coef := lreflCoef
alias to_poly_line_refl_coef := toPoly_lreflCoef
alias rho_lrefl_conj_p_poly_pow := rho_lrefl_conjPpoly_pow
alias pull_form_lrefl_seed := pullForm_lrefl_seed
alias pull_form_lrefl_conj_seed := pullForm_lrefl_conjSeed
alias refl_seed_inv := reflSeedInv
alias pull_form_lrefl_refl_seed := pullForm_lrefl_reflSeed
alias de_rham_class_refl_seed_inv := deRhamClass_reflSeedInv


/-! ### The seed class on `Λ₁⁺` and its identification with the entry section (LS11 to LS15)

`line_plus_group`/`line_plus_data` is `Λ₁⁺ = ℤ² ⋊ SL₂(ℤ)` with its `LineData` (pivoted Levi block, reversed bottom row).  `line_seed_rel_cocycle` is the relative 2-cocycle (zero on pairs of radical
elements) of the seed in the library's `linePlusRep n`; `line_complexify_cusp_seed_class` identifies the complexified de Rham class of `cuspSeedClass` with it.  `line_seed_edge` /
`line_conj_seed_edge` give the Hochschild-Serre edge of the seed and of the antiholomorphic seed as `-3 · Sw(ε)` (`edge_coordinate_line`), `edge_line_refl_rel` that of the reflection-invariant seed
`σ_f + (-1)ⁿ \overline{σ_{f^*}}` as `-6` times the restriction of the pivot-swap `dlCocycleOf n ψ_f`, `eq_seed_of_edge_line` the injectivity statement, and `line_seed_identity` the literal comparison: the
restriction to `Λ₁⁺` of the good-line coordinate of the entry section `a_li` is `(n+1)/2` times the complexified de Rham class of the reflection-invariant seed (`ε = 1`); `paper_line_seed_identity` is
the paper's section (`λ_li = -1`), whose scalar is `-(n+1)/2`. -/

open TernaryPeriodPolynomials.Argument.LineSeed in
alias line_seed_rel_cocycle := lineSeedRelCocycle
open TernaryPeriodPolynomials.Argument.LineSeed in
alias line_seed_conj_rel_cocycle := lineSeedConjRelCocycle
open TernaryPeriodPolynomials.Argument.LineSeed in
alias line_complexify := lineComplexify
open TernaryPeriodPolynomials.Argument.LineSeed in
alias line_complexify_cusp_seed_class := lineComplexify_cuspSeedClass
open TernaryPeriodPolynomials.Argument.LineSeed in
alias line_complexify_cusp_seed_conj_class := lineComplexify_cuspSeedConjClass
open TernaryPeriodPolynomials.Argument.LineSeed in
alias line_plus_edge_s_injective := linePlusEdgeS_injective
open TernaryPeriodPolynomials.Argument.LineSeed in
alias edge_coordinate_line := edge_coordinate_line
open TernaryPeriodPolynomials.Argument.LineSeed in
alias line_seed_edge := lineSeedEdge
open TernaryPeriodPolynomials.Argument.LineSeed in
alias line_conj_seed_edge := lineConjSeedEdge
open TernaryPeriodPolynomials.Argument.LineSeed in
alias line_refl_rel := lineReflRel
open TernaryPeriodPolynomials.Argument.LineSeed in
alias line_complexify_refl_seed := lineComplexify_reflSeed
open TernaryPeriodPolynomials.Argument.LineSeed in
alias edge_line_refl_rel := edge_lineReflRel
open TernaryPeriodPolynomials.Argument.LineSeed in
alias eq_seed_of_edge_line := eq_seed_of_edge_line
open TernaryPeriodPolynomials.Argument.LineSeed in
alias line_plus_res := linePlusRes
open TernaryPeriodPolynomials.Argument.LineSeed in
alias line_plus_edge_res_h2 := linePlusEdge_resH2
open TernaryPeriodPolynomials.Argument.LineSeed in
alias line_seed_identity := lineSeedIdentity
open TernaryPeriodPolynomials.Argument.LineSeed in
alias paper_line_seed_identity := paperLineSeedIdentity

/-! ### The Γ(N) passage (S1 parts B and D with S3): the line boundary vector of the entry section -/

open TernaryPeriodPolynomials.Argument.LineSeed in
alias pi_map := piMap
open TernaryPeriodPolynomials.Argument.LineSeed in
alias clean_hom := cleanHom
open TernaryPeriodPolynomials.Argument.LineSeed in
alias clean_mor := cleanMor
open TernaryPeriodPolynomials.Argument.LineSeed in
alias clean_complexify := clean_complexify
open TernaryPeriodPolynomials.Argument.LineSeed in
alias phi_line_at_clean := phiLineAt_clean
open TernaryPeriodPolynomials.Argument.LineSeed in
alias phi_line_at_of_res := phiLineAt_of_res
open TernaryPeriodPolynomials.Argument.LineSeed in
alias phi_line_at_good_line_class := phiLineAt_goodLineClass
open TernaryPeriodPolynomials.Argument.LineSeed in
alias phi_line_at_paper_line := phiLineAt_paperLine
open TernaryPeriodPolynomials.Argument.LineSeed in
alias line_face_seed_ker_class_level_n_smul := lineFaceSeedKerClass_levelN_smul
open TernaryPeriodPolynomials.Argument.LineSeed in
alias line_face_seed_conj_ker_class_level_n_smul := lineFaceSeedConjKerClass_levelN_smul
open TernaryPeriodPolynomials.Argument.LineSeed in
alias phi_line_at_good_line_class_bad := phiLineAt_goodLineClass_bad
open TernaryPeriodPolynomials.Argument.LineSeed in
alias line_entry_coeff := lineEntryCoeff
open TernaryPeriodPolynomials.Argument.LineSeed in
alias line_entry_tuple := lineEntryTuple
open TernaryPeriodPolynomials.Argument.LineSeed in
alias phi_line_eq_line_seed_boundary := phiLine_eq_lineSeedBoundary
open TernaryPeriodPolynomials.Argument.LineSeed in
alias phi_line_good_line_class := phiLine_goodLineClass

/-! ### Frame change: the line boundary vectors at every face (S1 P1 to P3 with S3's `seedComb_frame`) -/

open TernaryPeriodPolynomials.Argument.LineSeed in
alias exists_clean_frame := exists_clean_frame
open TernaryPeriodPolynomials.Argument.LineSeed in
alias phi_line_at_frame_clean := phiLineAt_frame_clean
open TernaryPeriodPolynomials.Argument.LineSeed in
alias phi_line_at_frame_of_res := phiLineAt_frame_of_res
open TernaryPeriodPolynomials.Argument.LineSeed in
alias line_entry_tuple_c := lineEntryTupleC
open TernaryPeriodPolynomials.Argument.LineSeed in
alias phi_line_eq_line_seed_boundary_c := phiLine_eq_lineSeedBoundaryC
open TernaryPeriodPolynomials.Argument.LineSeed in
alias phi_line_at_any_of_res := phiLineAt_any_of_res
open TernaryPeriodPolynomials.Argument.LineSeed in
alias phi_line_at_good_line_class_any := phiLineAt_goodLineClass_any
open TernaryPeriodPolynomials.Argument.LineSeed in
alias phi_line_good_line_class_uncond := phiLine_goodLineClass_uncond
open TernaryPeriodPolynomials.Argument.LineSeed in
alias phi_line_paper_line := phiLine_paperLine

end TernaryPeriodPolynomials.Argument.Statements.LineSeed
