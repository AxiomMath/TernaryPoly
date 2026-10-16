module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Jmath
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.PlaneInvolution
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Restrict
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Series
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Transport
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Cusps
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Coefficients
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Bridge
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.ModelDual
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.GammaNSeries
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.StandardCusp
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.LiteralDual
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.LiteralDualModel
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.ComplexifyGen
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Cuspidal
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.LiteralFacePairing
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.LiteralFacePairingPlane
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.LiteralFiberKoszul
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.CuspRows
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.CuspRowsCross
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.GramBridge
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.FlagReal
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Values
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.FlagZero
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.PD

@[expose] public section


/-!
# The dual series `ℰ_Q^∨` and the dual constant terms `ar:eq:dualconstantterms` (Appendix C.4)

Formalized by Claude Sonnet 5.5.

Paper: "The dual series and the boundary relation".

## What is proved

1. **`ȷ(g) = J (g⁻¹)ᵗ J` exchanges `P` and `Q`** (`jmath`, an involutive automorphism of `SL₃(ℤ)`): the plane stabilizer is carried to the
   line stabilizer and conversely, `Γ(N)` and the Borel group are preserved, and the cusp groups `Γ_{h⁻¹Ph}`, `Γ_{h⁻¹Qh}`, `Γ_{h⁻¹Bh}` go to
   `Γ_{ȷ(h)⁻¹Qȷ(h)}`, `Γ_{ȷ(h)⁻¹Pȷ(h)}`, `Γ_{ȷ(h)⁻¹Bȷ(h)}` (`jmath_mem_gammaNQ_iff` …, `jmath_mem_gammaNQAt_iff` …).
2. **`E ∘ ȷ` is the literal dual `E*` after the coordinate change by `J`**, for `E = E_{n,e}` as the library defines it
   (`GeneralEisenstein.homogeneousAction n e` on `Sym^n((ℂ³)*)`): `dualIso_equivariant : dualIso n (ρ(ȷ g) f) = ρ(g)^∨ (dualIso n f)`
   for all `g ∈ GL₃(ℂ)`, and `dualIso_dualRho` for the coefficient representation of `Γ`.  The scaling `Sym^n(V)* ≅ Sym^n(V*)` is the
   multinomial one (`symbol`, `eval_symbol`, `dualIso_monomial`, `dualIso_monomial_factorial`): `n! · (dualIso f)(X^t) = t! · f_{Jt}`.
3. **The dual series**: `dualSeriesInv` is the closed `Γ`-equivariant `E^∨`-valued two-form `ȷ̃^* ℰ_P(ω_f)` (the convergent series for
   `Γ' ⊇ ȷ(Γ)`, pulled back along the equivariant involution `jPlane` of `Ω ≅ 𝒳` by `EisensteinClass.deRhamClass_natural`), and
   `dualSeriesClass_eq : [ȷ̃^* ℰ] = H²(ȷ)[ℰ]`; `dualSeriesClass_gammaN` for `Γ(N)`, `dualSeriesAtClass` at every cusp and seed type.
4. **Transport of the constant terms** (unconditional): `dual_restrictions_transport` — the `r_Q` (resp. `r_P`, `r_B`) restriction of
   `ȷ^* c'` at `h` is the `ȷ`-pullback of the `r_P` (resp. `r_Q`, `r_B`) restriction of `c'` at `ȷ(h)`, for every `c' ∈ H²(Γ(N), E_n)`.
   `dual_constant_terms_transport`, `dual_constant_terms_series`, `dual_constant_terms_T`: the plane statements
   `r_P ℰ_P(ξ) = ξ, r_Q ℰ_P(ξ) = Tξ, r_B ℰ_P(ξ) = 0` (`ConstantTermsAt`) imply
   `r_Q ℰ_Q^∨(η) = η, r_P ℰ_Q^∨(η) = T^∨ η, r_B ℰ_Q^∨(η) = 0` with `η = ȷ^*ξ` and `T^∨ = ȷ^* ∘ T ∘ (ȷ^*)⁻¹` (`dualT`); no
   invertibility or adjoint normalization of `T`, `T^∨` is used.
5. **Target encodings connected to the literal dual.** The targets (`Targets/LemmaC2`, `Targets/FacePairing`, `NewRoute/PropC5`)
   encode `E*` as `E ∘ dualInvolution` (`dualInvolution g = levelScale · g^{-T} · levelScale⁻¹`) with the apolar `dualPairing`.
   `thetaModelEquiv : E ≃ₗ E*`, `w ↦ (v ↦ dualPairing v w)`, is equivariant (`thetaModel_equivariant`: `Θ(ρ_χ(φ g) w) = ρ_χ(g)^∨ Θ(w)`, with the
   character scalar of `dualPairing_invariant`) and carries `dualPairing` to the evaluation pairing `E ⊗ E* → ℂ` (`thetaModelEquiv_eval`).
   The two models are related by the fixed coordinate change: `ȷ = Ad(J · levelScale⁻¹) ∘ dualInvolution` (`FacePairingFull.DualJ.jmath_eq_conj`,
   over `ℂ`: `jGL_complexify_eq_conj`) and `dualPairing h u = n! · (dualIso (J a u)) h` (`dualPairing_eq_dualIso`, `thetaModel_eq_dualIso`).

6. **The first unconditional dual row.** `dual_rQ_standard` (`3 ≤ N`, `4 ≤ n`): at the STANDARD cusp (`h = 1`, line group
   `Γ_Q = Γ(N) ∩ Q(ℤ)`) and for the HOLOMORPHIC seed of a cusp form `f` of `Γ₂(N)`, `r_Q ℰ_Q^∨(ω_f) = η` with `η = ȷ^*[seed of f]`
   (`dualSeedClass`), obtained by transporting the `constant_term_identity` through `ȷ` (`resTo_standard`: the bridge between the `resP` on `gammaNP N` and `resTo (Γ_{1⁻¹P1})`, by `restrict_comp`).  The coefficient system is `E^∨ = E∘ȷ` (`dualRho`);
   the literal contragredient `E*` is reached through the equivariant isomorphism `dualIso` (`dualIso_dualRho`), i.e. the dual identities
   are proved for `E^∨` and carried to the literal dual `E*` by that explicit isomorphism (the induced map on `H²` is not packaged here).
   **Every line cusp, both seeds** (`CuspRows`, `3 ≤ N`, `4 ≤ n`): `resTo_cuspFace` identifies the group restriction `resTo (Γ_{h⁻¹Ph})` with the de Rham class of
   `cuspFaceForm N h` for every `h` (generalising `resTo_standard`); `resTo_plane_seed` is the `constant_term_identity_at(_conj)` in this form; `dualSeriesAtClass_gammaN`
   is `ℰ_Q^∨` at the line cusp `h⁻¹Qh` (`ȷ̃^*` of the series at the plane cusp `ȷ(h)`, seed type `b`); `dual_rQ_at`: `r_Q ℰ_Q^∨ = η` there with
   `η = dualSeedClassAt = ȷ^*(cuspSeedClassAt (ȷ h))`; `dual_rQ_at_literal`: the same for complex coefficients and the literal `E*` (`cxFaceDual`, `toLiteral`).
   **Cross-cusp line values** (`CuspRowsCross`, from the `faceClass_none/pos/neg`, `faceClass_true_*` through `ȷ`): the line restriction at `h⁻¹Qh` of the dual series
   at the line cusp `h'` is `0` when `ȷ(h')ȷ(h)⁻¹` has no cell (`dual_rQ_cross_none`, `_true_none`) and `dualSeedClassAt` of `f|A` (bottom entry `1`: `_pos`, `_true_pos`)
   or of the conjugate/reflected form (bottom entry `-1`: `_neg`, `_true_neg`), for both seeds.
   **The `r_B = 0` row** (`FlagReal`): the real/complex flag dictionary `resTo_flag_eq_zero_iff` (injectivity of complexification `cxGen_injective`, of pullback along a group
   isomorphism `map_mulEquiv_injective`, and the `faceFlagStab_map_eq_gammaNBAt`/`faceFlagStab_one_map`) turns the complex flag vanishing into the real vanishing
   `resTo_flag_zero_of_cuspidal`, `resTo_gammaNBAt_zero_of_cuspidal` (every flag group `gammaNBAt N h` is the standard flag over the plane cusp `h`), and
   `dual_rB_zero_of_cuspidal`: `r_B ℰ_Q^∨ = 0` at `h⁻¹Bh` as soon as the complexified plane restriction at `ȷ(h)` is mixed cuspidal (the transported cell seeds are, by
   the `CuspValues`).  **Unconditionally** (`DualFlagZero`): `series_plane_cuspidal` (the complexified plane restriction of the series at any cusp is mixed cuspidal at every plane cusp, by the exact values and
   `faceSeedSpan_le_cuspidalInH2`), `series_rB_zero` (`r_B ℰ_P = 0` on every `Γ(N) ∩ h⁻¹Bh`) and `dual_rB_zero` (`r_B ℰ_Q^∨ = 0` on every `Γ(N) ∩ h⁻¹Bh`, both seeds, every line cusp).  `r_P = T^∨ η` needs the line statement `r_Q ℰ_P = Tξ` (the `Γ(N)` line constant term): not proved here.
10. **Complex dual cusp values, linearity and seed spanning** (`DualValues`, for the `dualEisenstein_of_section`): `jPullC`, `jPullC_res` (complex transport), `dualClassC` (the
   complexified `ℰ_Q^∨` at the line cusp `h`, seed `b`), `dualSeedHolC/ConjC/C` (dual seed classes), `dualClassC_add/_smul` and `dualSeed*_add/_smul` (additivity and twisted
   homogeneity in the cusp form), `dualCuspValues : DualCuspValues N n hn` (membership in the dual seed span, vanishing for different orbits, the dual seed class for the same cusp, both
   seeds; the `ȷ`-transport of `FormClassK.cuspValues`), `mem_dualCuspidalQ_iff_seeds` / `dualSeedSpan_eq_dualCuspidalQ` (Eichler-Shimura spanning for the dual coefficients, unconditional)
   and the literal-contragredient versions `dualSeedLitC`, `mem_dualCuspidalQLiteral_iff_seeds`.
9. **The homogeneous model on `GL₃(ℝ)`-vertices** (`GramBridge`): `jReal` (`ȷ` on `GL₃(ℝ)`, `jReal_mapGL`), `dualRealCoeff = ρ_ℂ ∘ ȷ`, `jRealCocycle` (`F^∨(y) = F(ȷ y)`),
   `bridge_dual_gram`: for every closed `Γ(N)`-equivariant form `ω`, the complexified class of `ȷ̃^*ω` is the bridge of `jRealCocycle (gramCocycle ω)`
   (`dual_series_gram`, `dual_series_at_gram`: the actual dual series); the dual analogue of the `bridge_gramCocycle_eisenstein`.  The passage from `GL₃(ℝ)`-vertices to
   the rational cocycle model of `rationalLevel` is not established already for `ℰ_P` (the `FormSeriesEqModelLinear`) and is not made for the dual.

7. **Target statements transported to the literal contragredient** (only `thetaModelEquiv` is used): `lemma_C_2_literal` (Lemma C.2 for a global
   cocycle `c''` of `E* = (rationalCoefficientComponent n triv).dual`, paired by evaluation), `face_pairing_perfect_literal` (the perfect line pairing
   `ar:eq:facepair`), `dual_constant_terms_pointwise_literal` (the model's dual constant-term existence statement).  `Targets/PropC5` has no dual
   coefficient system and needs no transport.
   **Literal trace / face pairing** (`LiteralFacePairing`): `traceValueLit` is the model trace formula with the apolar pairing replaced by
   evaluation of an `E*`-valued line cocycle; `traceValueLit_eq : traceValueLit z w y'' = traceValue z w (fromLineStar (Θ⁻¹ y''))` (`Θ = thetaModelEquiv`,
   scalar exactly `1`); `planeLitEquiv : H²(plane; E) ≃ₗ H²(line; E*)`, `innerPlaneLitEquiv : innerClasses n .plane ≃ₗ innerClassesRep (E*) .line`;
   `facePairingLit := facePairing ∘ innerPlaneLitEquiv⁻¹` and `facePairingLit_eq_traceValueLit` (it is the literal trace on any representatives).
   The plane face is the mirror (`LiteralFacePairingPlane`): `traceValuePLit_eq`, `lineLitEquiv : H²(line; E) ≃ₗ H²(plane; E*)`,
   `innerLineLitEquiv : innerClasses n .line ≃ₗ innerClassesRep (E*) .plane`, `facePairingPLit := facePairingP ∘ innerLineLitEquiv⁻¹` and
   `facePairingPLit_eq_traceValuePLit`.  The torus-fibre factor: `latticeKoszulLit` (`LiteralFiberKoszul`) is the Koszul data of a radical lattice for
   `E` and the literal `E*` paired by evaluation (`evPairing_invariant`), perfect in both arguments (`latticeKoszulLit_perfect`), and
   `latticeKoszulLit_eq_kostant` identifies it with `kostant (evPairing n) Ω.σ f g` (the generic `kostant_eq_koszul` already holds for arbitrary
   representations and pairings, so it applies to `E*` unchanged).  Finally `facePairing_literal_dual`: the `facePairing_literal` of
   `Statements.FacePairingPD` (one constant `c ≠ 0`; line and plane geometric pairings; even and odd Koszul-constant formulas for both the line and the plane face) restated with
   `facePairingLit`, `facePairingPLit` on classes of the literal `E*`.  Its geometric pairings and parabolic dictionary classes are those of
   `Statements.FacePairingPD` evaluated at the model class `innerPlaneLitEquiv⁻¹ η`, `innerLineLitEquiv⁻¹ β`: nothing geometric is redefined for `E*`.

8. **`𝒞_Q(E*)` and complexification.** `dualCuspidalQ` / `dualCuspidalQLiteral` (the mixed cuspidal group of the dual coefficient system at the line
   cusp `h⁻¹Qh`: the paper's construction applied at the plane cusp `ȷ(h)⁻¹Pȷ(h)` and pulled back along `ȷ`, then carried to the literal `E*` by `dualIso`,
   `toLiteral`, a bijection on `H²`); `cxGen` / `cxGen_map` (complexification of the real classes for an arbitrary coefficient pair);
   `rQ_mem_dualCuspidalLiteral` (the complexified line restriction of the dual of `c'` lies in `𝒞_Q(E*)` whenever the complexified plane restriction of `c'`
   at `ȷ(h)` is mixed cuspidal); `dual_rQ_standard_literal` (`r_Q ℰ_Q^∨ = η` at the standard cusp, complex coefficients, literal `E*`).

## What is NOT proved

* The plane statements `r_Q ℰ_P = Tξ` and `r_B ℰ_P = 0` for the actual series `ℰ_P(ω_f)` (items 6 and 9 above: only the `r_P`/line rows of the dual, i.e. the plane face
  values of `ℰ_P`, are proved, own cusp and cross-cusp); the dual `r_P = T^∨η` and `r_B = 0` rows are conditional on them (`dual_constant_terms_series`).
* `𝒞_Q(E*)` is defined by transport from `𝒞_P` (as in the paper), not intrinsically by Hochschild–Serre for the coefficient `E*`; the `lineFaceCuspidalInH2` is for `E_n`.
* The bridge from the specific class `ȷ̃^* ℰ_P` in `H²(Γ(N), E^∨)` to the boundary-building cochain model of `FacePairingFull/Dual` (rational cocycle model
  of the level group `rationalLevel`): only the coefficient-level link (`dual_constant_terms_pointwise_literal`) and the real-vertex bridge (`bridge_dual_gram`) are proved;
  for `ℰ_P` itself the passage from `GL₃(ℝ)`-vertices to `rationalLevel` is not established (the `FormSeriesEqModelLinear`).
-/

namespace TernaryPeriodPolynomials.Argument.Statements.EisensteinDual

open TernaryPeriodPolynomials.Argument.EisensteinDual

alias jmath_exchanges_plane_line := jmath_mem_lineStab_iff
alias jmath_exchanges_line_plane := jmath_mem_planeStab_iff
alias jmath_preserves_borel := jmath_mem_borelStab_iff
alias jmath_preserves_gammaN := jmath_mem_gammaN
alias jmath_gammaNQ_gammaNP := jmath_mem_gammaNQ_iff
alias jmath_gammaNP_gammaNQ := jmath_mem_gammaNP_iff
alias jmath_gammaNQAt_gammaNPAt := jmath_mem_gammaNQAt_iff
alias jmath_gammaNPAt_gammaNQAt := jmath_mem_gammaNPAt_iff
alias jmath_gammaNBAt := jmath_mem_gammaNBAt_iff

alias E_circ_jmath_equiv_dual := dualIso_equivariant
alias E_circ_jmath_equiv_dual_gamma := dualIso_dualRho
alias dual_scaling_monomial := dualIso_monomial_factorial

alias dual_series_class := dualSeriesClass_eq
alias dual_series_class_gammaN := dualSeriesClass_gammaN_eq

alias dual_constant_terms_of_plane := dual_constant_terms_series
alias dual_constant_terms_with_T := dual_constant_terms_T
alias dual_rQ_standard_cusp := dual_rQ_standard
alias resP_resTo_bridge := resTo_standard

alias model_equivariant := thetaModel_equivariant
alias model_eval := thetaModelEquiv_eval
alias models_agree := dualPairing_eq_dualIso
alias jmath_conj_dualInvolution := jGL_complexify_eq_conj
alias lemma_C_2_for_dual := lemma_C_2_literal
alias face_pairing_for_dual := face_pairing_perfect_literal
alias dual_constant_terms_for_dual := dual_constant_terms_pointwise_literal
alias dual_cuspidal_Q := dualCuspidalQLiteral
alias dual_rQ_mem_cuspidal := rQ_mem_dualCuspidalLiteral
alias dual_rQ_standard_for_dual := dual_rQ_standard_literal
alias dual_rQ_every_cusp := dual_rQ_at
alias dual_rQ_every_cusp_for_dual := dual_rQ_at_literal
alias dual_series_at_line_cusp := dualSeriesAtClass_gammaN_eq
alias plane_seed_at_cusp := resTo_plane_seed
alias resTo_cusp_face := resTo_cuspFace
alias dual_rQ_cross_cusp_none := dual_rQ_cross_none
alias dual_rQ_cross_cusp_pos := dual_rQ_cross_pos
alias dual_rQ_cross_cusp_neg := dual_rQ_cross_neg
alias dual_rQ_cross_cusp_true_none := dual_rQ_cross_true_none
alias dual_rQ_cross_cusp_true_pos := dual_rQ_cross_true_pos
alias dual_rQ_cross_cusp_true_neg := dual_rQ_cross_true_neg
alias dual_series_homogeneous_cocycle := bridge_dual_gram
alias dual_series_gram_cocycle := dual_series_gram
alias dual_series_at_gram_cocycle := dual_series_at_gram
alias dual_cusp_values := dualCuspValues
alias dual_class_add := dualClassC_add
alias dual_class_smul := dualClassC_smul
alias dual_seed_add := dualSeedC_add
alias dual_seed_smul := dualSeedC_smul
alias dual_cuspidal_Q_seeds := mem_dualCuspidalQ_iff_seeds
alias dual_seed_span := dualSeedSpan_eq_dualCuspidalQ
alias dual_cuspidal_Q_literal_seeds := mem_dualCuspidalQLiteral_iff_seeds
alias real_flag_vanishing_iff := resTo_flag_eq_zero_iff
alias dual_rB_zero_of_cuspidal_plane := dual_rB_zero_of_cuspidal
alias series_flag_zero := series_rB_zero
alias series_plane_restriction_cuspidal := series_plane_cuspidal
alias dual_flag_zero := dual_rB_zero
alias trace_value_literal := traceValueLit_eq
alias face_pairing_literal_trace := facePairingLit_eq_traceValueLit
alias inner_plane_line_literal := innerPlaneLitEquiv
alias trace_value_plane_literal := traceValuePLit_eq
alias face_pairing_plane_literal_trace := facePairingPLit_eq_traceValuePLit
alias inner_line_plane_literal := innerLineLitEquiv
alias koszul_lattice_literal := latticeKoszulLit
alias koszul_lattice_literal_perfect := latticeKoszulLit_perfect
alias koszul_lattice_literal_eq_kostant := latticeKoszulLit_eq_kostant

section FacePairingLiteral

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Argument.Statements.LemmaC2Geometric
open TernaryPeriodPolynomials.BoundaryDuality
open TernaryPeriodPolynomials.Argument.FacePairingFull.Dual
open TernaryPeriodPolynomials.Argument.Statements.FacePairing
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality

/-- **`ar:eq:facepair` for the literal contragredient `E*`**: the target statement `facePairing_literal`
transported along the explicit isomorphisms `innerPlaneLitEquiv : 𝒞_Q-model(E^φ) ≃ 𝒞_Q(E*)` and `innerLineLitEquiv : 𝒞_P-model(E^φ) ≃ 𝒞_P(E*)`
(`Θ ∘ (c ↦ c∘φ)`, `Θ = thetaModelEquiv`), so that the pairings are `facePairingLit : 𝒞_Q(E) × 𝒞_Q(E*) → ℂ` and
`facePairingPLit : 𝒞_P(E) × 𝒞_P(E*) → ℂ`.  The geometric pairings `geoLinePairing`, `geoPlanePairing` and the parabolic dictionary classes remain the
model-side objects of `Statements.FacePairingPD`, evaluated at the model class corresponding to the literal one. -/
theorem facePairing_literal_dual : ∃ c : ℂ, c ≠ 0 ∧
    (∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (b : innerClasses n .line)
      (η : innerClassesRep (rationalCoefficientComponent n trivialCharacter).dual .line),
      r (c⁻¹ * facePairingLit n b η) = geoLinePairing n r b ((innerPlaneLitEquiv n).symm η)) ∧
    (∀ (n : ℕ) (r : ℂ →ₗ[ℚ] ℚ) (ξ : innerClasses n .plane)
      (β : innerClassesRep (rationalCoefficientComponent n trivialCharacter).dual .plane),
      r ((-c)⁻¹ * facePairingPLit n ξ β) = geoPlanePairing n r ξ ((innerLineLitEquiv n).symm β)) ∧
    (∀ (n : ℕ) (hn : 0 < n) (heven : Even n) (r : ℂ →ₗ[ℚ] ℚ) (b : innerClasses n .line)
      (η : innerClassesRep (rationalCoefficientComponent n trivialCharacter).dual .line),
      r (c⁻¹ * facePairingLit n b η) = r (c⁻¹ * ((((n + 1).factorial : ℂ) / 3) *
        LocalPairingCaseL0Even.badGoodPairingEven heven (Literal.badLineParabolic hn b)
          (Literal.goodPlaneParabolic hn ((innerPlaneLitEquiv n).symm η))))) ∧
    (∀ (n : ℕ) (hn : 0 < n) (hodd : Odd n) (r : ℂ →ₗ[ℚ] ℚ) (b : innerClasses n .line)
      (η : innerClassesRep (rationalCoefficientComponent n trivialCharacter).dual .line),
      r (c⁻¹ * facePairingLit n b η) = r (c⁻¹ * (
        (-((n + 1).factorial : ℂ) / 3) * LocalPairingCaseL0Odd.badGoodPairingOdd hodd (Literal.badLineParabolic hn b)
            (Literal.goodPlaneParabolic hn ((innerPlaneLitEquiv n).symm η)) +
        ((n + 1).factorial : ℂ) * ParabolicDuality.LevelOne.parabolicPairing
          (ParabolicDuality.LevelOne.twistedPairing_goodLine_trivial hodd) (Literal.goodLineParabolic hn b)
          (Literal.badPlaneParabolic hn hodd ((innerPlaneLitEquiv n).symm η))))) ∧
    (∀ (n : ℕ) (hn : 0 < n) (heven : Even n), ∃ a : ℂ, (a = 1 ∨ a = -1) ∧
      ∀ (r : ℂ →ₗ[ℚ] ℚ) (ξ : innerClasses n .plane)
        (β : innerClassesRep (rationalCoefficientComponent n trivialCharacter).dual .plane),
        r ((-c)⁻¹ * facePairingPLit n ξ β) = r ((-c)⁻¹ * (a * ((((n + 1).factorial : ℂ) / 3) *
          LocalPairingCaseL0Even.badGoodPairingEven heven
            (Literal.badLineParabolic hn ((innerLineLitEquiv n).symm β)) (Literal.goodPlaneParabolic hn ξ))))) ∧
    (∀ (n : ℕ) (hn : 0 < n) (hodd : Odd n), ∃ a : ℂ, (a = 1 ∨ a = -1) ∧
      ∀ (r : ℂ →ₗ[ℚ] ℚ) (ξ : innerClasses n .plane)
        (β : innerClassesRep (rationalCoefficientComponent n trivialCharacter).dual .plane),
        r ((-c)⁻¹ * facePairingPLit n ξ β) = r ((-c)⁻¹ * (a * (
          (-((n + 1).factorial : ℂ) / 3) * LocalPairingCaseL0Odd.badGoodPairingOdd hodd
              (Literal.badLineParabolic hn ((innerLineLitEquiv n).symm β)) (Literal.goodPlaneParabolic hn ξ) +
          ((n + 1).factorial : ℂ) * ParabolicDuality.LevelOne.parabolicPairing
            (ParabolicDuality.LevelOne.twistedPairing_goodLine_trivial hodd)
            (Literal.goodLineParabolic hn ((innerLineLitEquiv n).symm β))
            (Literal.badPlaneParabolic hn hodd ξ))))) := by
  refine (TernaryPeriodPolynomials.Argument.Statements.FacePairingPD.facePairing_literal).elim (fun c hc => ?_)
  have h1 := hc.2.1
  have h2 := hc.2.2.1
  have h3 := hc.2.2.2.1
  have h4 := hc.2.2.2.2
  have e1 : ∀ (n : ℕ) (b : innerClasses n .line)
      (η : innerClassesRep (rationalCoefficientComponent n trivialCharacter).dual .line),
      facePairingLit n b η = facePairing n b ((innerPlaneLitEquiv n).symm η) := fun _ _ _ => rfl
  have e2 : ∀ (n : ℕ) (ξ : innerClasses n .plane)
      (β : innerClassesRep (rationalCoefficientComponent n trivialCharacter).dual .plane),
      facePairingPLit n ξ β = Plane.facePairingP n ξ ((innerLineLitEquiv n).symm β) := fun _ _ _ => rfl
  refine ⟨c, hc.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n r b η
    exact (congrArg (fun z => r (c⁻¹ * z)) (e1 n b η)).trans (h1 n r b _)
  · intro n r ξ β
    exact (congrArg (fun z => r ((-c)⁻¹ * z)) (e2 n ξ β)).trans (h2 n r ξ _)
  · intro n hn heven r b η
    exact (congrArg (fun z => r (c⁻¹ * z)) (e1 n b η)).trans ((h1 n r b _).trans (h3 n hn heven r b _))
  · intro n hn hodd r b η
    exact (congrArg (fun z => r (c⁻¹ * z)) (e1 n b η)).trans ((h1 n r b _).trans (h4 n hn hodd r b _))
  · intro n hn heven
    exact (TernaryPeriodPolynomials.Argument.Statements.FacePairingPD.geoPlanePairing_literal_even c h2 n hn heven).elim
      (fun a ha => ⟨a, ha.1, fun r ξ β =>
        (congrArg (fun z => r ((-c)⁻¹ * z)) (e2 n ξ β)).trans ((h2 n r ξ _).trans (ha.2 r ξ _))⟩)
  · intro n hn hodd
    exact (TernaryPeriodPolynomials.Argument.Statements.FacePairingPD.geoPlanePairing_literal_odd c h2 n hn hodd).elim
      (fun a ha => ⟨a, ha.1, fun r ξ β =>
        (congrArg (fun z => r ((-c)⁻¹ * z)) (e2 n ξ β)).trans ((h2 n r ξ _).trans (ha.2 r ξ _))⟩)

end FacePairingLiteral

end TernaryPeriodPolynomials.Argument.Statements.EisensteinDual
