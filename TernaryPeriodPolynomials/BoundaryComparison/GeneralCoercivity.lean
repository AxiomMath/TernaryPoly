module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Main
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.Complex
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.ComplexForms
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.ComplexDual
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.ComplexLiteralDual
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.LiteralForms
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.CoveringSingular
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.ComplexBaseChange
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.RationalDual
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.SmoothInduction
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.GeneralSingular
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.NeatSingular
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.ComplexCochains
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.DescentSingular
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.ComplexGeneral
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.DualMain
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.DualFaithful
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.DualDictionary
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.DetTwist
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.Frozen
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Descent
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.FrozenPrimitive
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.PrimGlobal
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.PrimCoeff

@[expose] public section


/-!
# Proposition C.1 (`ar:prop:coercivity`): coercivity and the vanishing of `H²_c → H²`

Paper: Proposition C.1: *for every `n > 0` there is `c_n > 0`, independent of `Γ`, such that every compactly
supported smooth `E`-valued form on `X_Γ` satisfies `‖Dω‖² + ‖D*ω‖² ≥ c_n ‖ω‖²`; consequently
`H²_c(X_Γ, E) → H²(X_Γ, E)` is zero; the conclusion holds for either determinant twist after descent
from a neat normal subgroup*, for `E = Sym^n ℂ³` or its dual.

## Dictionary

* `Γ` is an `Admissible` subgroup of `GL₃(ℝ)`: determinant one, free action on the symmetric space
  `Space` (trace-one positive matrices) with finite compact transporters.  It contains the neat
  principal congruence subgroups of level divisible by three, their subgroups, their real and
  rational `GL₃` conjugates, and the Cartan images `θΓ` (`admissible_principalReal`, `Admissible.mono`,
  `Admissible.conj`, `Admissible.theta`).
* `CForm Γ n k`: smooth `Γ`-equivariant `k`-forms on the positive coordinates with values in
  `Coefficients n = Sym^n ℝ³` (the substitution action `q ↦ q ∘ g⁻¹`) whose closed support in the
  orbit space `OrbitSpace Γ` is compact; `CForm.d` is the exterior derivative `D`, `CForm.delta`
  the formal `L²`-adjoint `D*` for the genuine Riemannian density and the Fischer metric, `normSq`
  the integrated norm over `quotientVolume Γ`.
* Complex coefficients: `CFormCx` (forms with values in the homogeneous polynomials of degree `n` over
  `ℂ`, Hermitian Fischer metric `formPairingC`), identified with pairs of real forms by `cxEquiv`;
  dual coefficients: `DForm` (forms for `ρ ∘ θ`, `θ g = (g⁻¹)ᵀ`, with the dual flat metric), identified
  with standard forms of `θΓ` by `dualEquiv`; `CFormCxD` their complexification.  The dual metric is
  the paper's `‖ρ*(g)⁻¹ p‖` (`coordinateCoefficientBilin_iotaC_frame`), `ρ ∘ θ` is the
  contragredient of the Fischer-dual of `Sym^n ℂ³` (`toDual_rhoC_theta`), and the dual operator norm
  gives the Hermitian dual metric (`dualNorm_metric_frame`).

## What is proved

* Coercivity (`prop_c1_real`, `prop_c1_complex`, `prop_c1_dual`, `prop_c1_complex_dual`,
  `prop_c1_frozen_cover`): one constant `c_n > 0` for all admissible `Γ`, in every degree, for
  `Sym^n ℝ³`, `Sym^n ℂ³`, and their duals; consistency with the `Core`/Hilbert objects of the
  cover `Γ(6) ∩ K` (`frozen_consistency`).
* Vanishing of `H²_c → H²` in de Rham form for every admissible `Γ` and `n > 0`
  (`vanishing_real`, `vanishing_complex`, `vanishing_dual`, `vanishing_complex_dual`): every closed
  `ζ ∈ CForm Γ n 2` is `dη` for a smooth `Γ`-equivariant one-form `η` (not compactly supported).
  The chain is: coercivity ⟹ `L²` Hodge theory in the completion (Gaffney's lemma, TierB) ⟹ a weak
  `L²` primitive (`Admissible.closed_has_weak_primitive`) ⟹ a `Γ`-invariant functional on test
  one-forms ⟹ a smooth equivariant primitive by local weak Poincaré on coordinate boxes, Weyl's lemma
  and an equivariant partition of unity (`exists_smooth_primitive`).
* Determinant twists and descent: a smooth `Γ'`-equivariant primitive for `Γ' ∩ Γ` normal of finite
  index in `Γ` descends to a smooth `Γ`-(twisted-)equivariant primitive by averaging over `Γ/Γ'`
  (`vanishing_descent`, `vanishing_twisted_descent`); the determinant-twist character is trivial on
  `Γ`.  For every admissible `Γ ⊇ gamma0` (the cover) with `gamma0` normal of finite index,
  `vanishing_frozen_supergroup`, `vanishing_frozen_supergroup_twisted`.

## Dependencies

Nothing here uses Eisenstein cohomology, the old Eisenstein assembly, the old odd-alternating
certificate, or `TernaryPeriodPolynomials`.  The proof of the vanishing for general `Γ`
uses, from the original the original library library, only its Γ-free coordinate weak-regularity
package (`coordinateTestBox_weak_primitive_mod_smooth`,
`coordinateTestBox_zeroForm_smooth_of_smooth_exterior`, `formWeakExterior_regular`,
`valuedRegularCurrent_eq_iff`) and the abstract Hilbert-complex / Friedrichs mollifier modules, not
the quotient-manifold layer.  `vanishing_frozen_supergroup*` additionally rests on the theorem
`TernaryPoly.PolynomialFormWeakSmooth.positive_degree_compact_smooth_exact` through `frozenEquiv`.

## The actual singular compact-to-ordinary map (fixed deck group)

`Variants/CoveringSingular` instantiates the global APIs of the original library
(`SmoothSingularGlobalCompactForgetComparison`, `...OriginalSmoothComparison`,
`...CompactExactVanishing.originalCompactForget_eq_zero_of_smooth_exact`) for the fixed deck group
`DeckGroup = principalSixInK` (the cover `gamma0 = principalSixInKReal`) and the genuine
`compactConvexCover`.  The smooth exactness hypothesis `CompactExactInDegree` is proved from the
Tier B theorems through the identification `coveringEquiv` of the covering de Rham complex with the
generic equivariant form spaces (`coveringReal/Dual/Cx/CxD/Lit`, compatible with the differential and
with compact support), and the rational deck-group systems are linked to the form-side coefficient
spaces by equivariant isomorphisms of their real scalar extensions: real `Sym^n`
(`singular_real`), dual (`singular_dual`, polynomials in the basis vectors with `gᵀ` acting), complex
`Sym^n ℂ³` as the doubled rational system (`singular_complex`, the complex-forget dictionary through
`reImEquiv`; the library has no `ℂ`-coefficient singular cohomology, so the complex statement is made for
the real-coefficient singular cohomology of the real forget of `Sym^n ℂ³`, see the next section),
complexified dual (`singular_complex_dual`), and the literal `ℂ`-linear dual
`StrongDual ℂ (Sym^n ℂ³)` with the contragredient action (`singular_lit`, via `litRealEquiv`).  The
interior-cover transfers are `singular_*_interior`.  None of this uses the exactness theorem
`positive_degree_compact_smooth_exact`.

## Complex coefficients: the real-coefficient singular map of the complex forget

`Variants/ComplexBaseChange`.  The actual complex-valued singular-cochain differential, support and primitive transport to the real
forget remain to be assembled. The library has the actual real-coefficient singular compact-to-ordinary
map for the fixed deck group (`TernaryPoly.SmoothSingularGlobal.realCoverCompactForget`); the zero theorem
below is proved directly for this map.
The canonical coefficientwise equivalences `complexDeckEquiv`, `complexDualDeckEquiv` (real and imaginary
coordinates) identify the real scalar extension of the doubled rational systems with `Sym^n ℂ³` and its
complexified dual, equivariantly (`complex_dictionary_equivariant`) and with the complex structure
(`complex_dictionary_J`: `J (a, b) = (-b, a)` corresponds to multiplication by `i`; the deck action is
`ℂ`-linear, `Tcx_comm_cxI`).  The real-coefficient singular maps vanish for all five systems, directly from
smooth exactness and the smooth/singular comparison `realCompactSmoothComparison_forget` (no rational class
and no injectivity is involved): `singular_realcoeff_*`.  The rational maps then follow by injectivity
(`singular_complex_of_real`, `singular_complex_dual_of_real`), and `V ⊕ V` has vanishing `compactForget`
iff `V` has, for the deck group and for every admissible `Γ` (`singular_double_iff`,
`singular_double_iff_general`).  The `ℂ`-vector space structure on the singular classes (functoriality of
`realCoverCompactCohomology` in the coefficients) is not constructed; the real-coefficient singular
cohomology of the library exists only for the fixed deck group.

## The actual singular map for every permitted arithmetic group (finite-cover and coefficient descent)

`Variants/SmoothInduction` proves the smooth Shapiro lemma `compactExact_induced`: for a finite-index
admissible subgroup `H` of the cover, the induced real representation `indReal T hle` of the
deck group on `FDeck/H → F` is smoothly exact in degree one as soon as `T` has the primitive property
over `H` (`PrimitiveProperty`; the five systems have it by Tier B, `primitive_real` ... `primitive_lit`).
With the rational Shapiro lemma `singularVanish_of_deck_ind` and the characteristic-zero transfer
`singularVanish_of_subgroup` (`Singular/{Transfer,Cover,Orbit,DeckLink}`, on the intrinsic model
`compactForget_two_eq_zero_iff_funVanish`) this gives `singularVanish_of_primitive`, and
`Variants/GeneralSingular` the final statements `SingularVanish Γ hΓ A` for the systems
`realSystem/dualSystem/complexSystem/complexDualSystem κ` of any admissible `Γ` with a rational
structure `κ` that is commensurable with `gamma0` (`singular_real_of_comm`, ...), concretely for
every principal congruence subgroup `Γ(N)`, `3 ∣ N`, `N > 0` (`singular_principal_*`) and every
rational conjugate `g Γ(N) g⁻¹`, `g ∈ GL₃(ℚ)` (`singular_conj_*`).  The dual rational system is
`ℚ`-isomorphic to the genuine contragredient `Hom_ℚ(A, ℚ)` (`Variants/RationalDual`,
`dual_is_rational_contragredient`).

## Scope of the paper's Proposition `ar:prop:coercivity`

The paper applies it to a neat principal congruence subgroup `Γ ⊂ SL₃(ℤ)` of level divisible by three
and its rational conjugates ("the convention is unchanged for a rational
conjugate"), and in the proof of `thm:boundary-evaluation` to a neat normal (congruence) subgroup
`Γ' ⊂ K ∩ SL₃(ℤ)`; determinant twists are trivial on `SL₃` and finite-group
averaging descends the primitive from a neat normal cover.  `Variants/NeatSingular` proves
the singular vanishing for **every** finite-index subgroup of `SL₃(ℤ)` that is neat in the paper's
sense (`singular_neatSL_*`, via `neat_torsionFree` and the admissibility of torsion-free subgroups), for
every rational conjugate (`singular_neatConj_*`), and in particular for all `Γ(N)` with `N ≥ 3`
(`singular_gammaN_*`, neatness from `ConvergenceC4.gammaN_isNeat`).  Normality in `K` or `K†` is not used.

## Complex-valued cochains and descent to the non-neat groups

`Variants/ComplexCochains`: for the fixed deck group, the closed equivariant complex-valued (`Sym^n ℂ³`,
resp. dual, complexified dual, literal dual) singular 2-cochains of `CoverOpen univ` that vanish on all
simplices of `CoverOpen Kᶜ` have equivariant primitives (`cochain_primitive_*`), by transport along the
canonical coefficient equivalence of the real compact-forget vanishing; the transport commutes with the
alternating-face differential, equivariance and the support condition.

`Variants/DescentSingular`: for `K`, `K ∩ SL₃(ℤ)` and `GL₃(ℤ)` and the coefficient systems
`E_{n,t}` including the determinant twist (`e = -t`), the equivariant compact-to-ordinary vanishing
`EquivSingularVanish` holds by rational transfer/averaging over `Γ/Γ'` from the neat cover
`Γ' = Γ(6) ∩ SL₃(ℤ)` (`singular_descent`, `singular_descent_*`, `singular_K`, `singular_kSL`,
`singular_GL`).  For free groups `EquivSingularVanish` is `SingularVanish` (`equiv_singular_iff`).  The smooth
counterpart (primitive averaged over `Γ/Γ'`, real twist `det^{-e}`) is `TierB/Descent`.

## What is not proved here

The complex systems use doubled rational models, whose real scalar extensions identify with complex
coefficients through real and imaginary coordinates (`ℂ = ℝ ⊕ ℝ i` as real vector spaces);
the library has no singular cohomology with `ℂ` coefficients, and the comparison with the complex local
system is made for the real forget on the fixed deck group (`Variants/ComplexBaseChange`); for general
`Γ` the doubled model is shown equivalent to the rational one (`singular_double_iff_general`).  The singular statements are for subgroups of
`GL₃(ℝ)` that are admissible, rational and commensurable with `Γ(6)`; non-neat groups are not
covered (see below).  Determinant twists enter the real/complex systems through the parameter `e`;
on determinant-one groups the twist character is trivial.

Non-neat groups with torsion are not `Admissible` (the action on `Space` is not free); for them the
statement is the descent from a neat normal subgroup (`vanishing_descent`), which needs no
admissibility, and no orbifold forms are formalized.  The literal `ℂ`-linear dual-valued forms
(`LitForm`, values in `LitCoeff n = StrongDual ℂ (Sym^n ℂ³)` with the contragredient action
`litRep n g φ = φ ∘ ρ_ℂ(g)⁻¹` and the dual operator norm) are identified with `CFormCxD` by the
Fischer-Riesz map (`litForms`, intertwining `ρ_ℂ ∘ θ` with `litRep`, `litPhi_equivariant`); the
exterior derivative `LitForm.d` (`LitForm.d_apply`: the pointwise `extDeriv`), the `L²` pairing
`litL2` and the formal adjoint `IsLitFormalAdjoint` are transported along it.  The `L²` pairing is
therefore defined through the Hermitian dual metric of `CFormCxD`; its coefficient part is the literal
dual norm by `litCoeff_normSq_frame` (and `dual_norm_metric`), but the exterior-power part of the
pointwise metric is not re-derived on `LitCoeff`-valued forms.  Coercivity and the vanishing for
`LitForm` are `lit_coercivity` and `vanishing_lit`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.GeneralCoercivity

open TernaryPeriodPolynomials.Argument.GeneralCoercivity

/-! ### Coercivity -/

alias prop_c1_real := general_coercivity
alias prop_c1_complex := general_coercivity_complex_forms
alias prop_c1_dual := general_coercivity_dual
alias prop_c1_complex_dual := general_coercivity_complex_dual
alias lit_coercivity := general_coercivity_lit
alias prop_c1_frozen_cover := coercivity_frozen_cover
alias frozen_consistency := frozenCoercive_iff

/-! ### Vanishing of `H²_c → H²` -/

alias vanishing_real := Admissible.closed_compact_exact
alias vanishing_complex := Admissible.closed_compact_exact_complex
alias vanishing_dual := Admissible.closed_compact_exact_dual
alias vanishing_complex_dual := Admissible.closed_compact_exact_complex_dual
alias vanishing_lit := Admissible.closed_compact_exact_lit

/-! ### Determinant twists and descent -/

alias vanishing_descent := exists_equivariant_primitive_of_normal
alias vanishing_twisted_descent := exists_twisted_primitive_of_normal
alias vanishing_frozen_supergroup := closed_compact_exact_of_frozen_normal
alias vanishing_frozen_supergroup_twisted := closed_compact_exact_twisted_of_frozen_normal

/-! ### The dual metric -/

/-! ### The actual singular compact-to-ordinary map for the fixed deck group -/

alias singular_real := real_compactForget_zero
alias singular_dual := dual_compactForget_zero
alias singular_complex := complex_compactForget_zero
alias singular_complex_dual := complex_dual_compactForget_zero
alias singular_lit := lit_compactForget_zero
alias singular_real_interior := real_interior_compactForget_zero
alias singular_dual_interior := dual_interior_compactForget_zero
alias singular_complex_interior := complex_interior_compactForget_zero
alias singular_complex_dual_interior := complex_dual_interior_compactForget_zero
alias singular_realcoeff_real := real_realCompactForget_zero
alias singular_realcoeff_dual := dual_realCompactForget_zero
alias singular_realcoeff_complex := complex_realCompactForget_zero
alias singular_realcoeff_complex_dual := complex_dual_realCompactForget_zero
alias singular_realcoeff_lit := lit_realCompactForget_zero
alias singular_complex_of_real := complex_compactForget_zero_of_real
alias singular_complex_dual_of_real := complex_dual_compactForget_zero_of_real
alias singular_double_iff := compactForget_double_zero_iff
alias singular_double_iff_general := singularVanish_double_iff
alias complex_dictionary_equivariant := complexDeckEquiv_equivariant
alias complex_dictionary_J := complexDeckEquiv_J
alias cochain_primitive_real := real_cochain_primitive
alias cochain_primitive_dual := dual_cochain_primitive
alias cochain_primitive_complex := complex_cochain_primitive
alias cochain_primitive_complex_dual := complex_dual_cochain_primitive
alias cochain_primitive_lit := lit_cochain_primitive
alias equiv_singular_iff := equivSingularVanish_iff
alias singular_descent := equivSingularVanish_of_finiteIndex
alias singular_descent_real := equivSingularVanish_paper_real
alias singular_descent_dual := equivSingularVanish_paper_dual
alias singular_descent_complex := equivSingularVanish_paper_complex
alias singular_descent_complex_dual := equivSingularVanish_paper_complex_dual
alias singular_K := equivSingularVanish_K
alias singular_kSL := equivSingularVanish_kSL
alias singular_GL := equivSingularVanish_GL
alias complex_valued_deck := equivVanish_deck_of_cochainPrimitive
alias complex_valued_shapiro := equivVanish_res_of_ind
alias complex_valued_of_primitive := equivVanish_of_primitive
alias complex_valued_of_comm := equivVanish_of_comm
alias complex_valued_explicit := equivVanish_qRep_iff
alias complex_valued_twisted_descent := equivVanish_twisted_descent
alias complex_valued_real_of_comm := equivVanish_real_of_comm
alias complex_valued_dual_of_comm := equivVanish_dual_of_comm
alias complex_valued_complex_of_comm := equivVanish_complex_of_comm
alias complex_valued_complex_dual_of_comm := equivVanish_complex_dual_of_comm
alias complex_valued_lit_of_comm := equivVanish_lit_of_comm
alias complex_valued_principal_complex := equivVanish_principal_complex
alias complex_valued_conj_complex := equivVanish_conj_complex
alias complex_valued_neat_complex := equivVanish_neat_complex
alias complex_valued_neatConj_complex := equivVanish_neatConj_complex
alias complex_valued_neatSL_complex := equivVanish_neatSL_complex
alias complex_valued_gammaN_complex := equivVanish_gammaN_complex
alias complex_valued_K_complex := equivVanish_K_complex
alias complex_valued_kSL_complex := equivVanish_kSL_complex
alias complex_valued_GL_complex := equivVanish_GL_complex
alias complex_valued_principal_complex_dual := equivVanish_principal_complex_dual
alias complex_valued_conj_complex_dual := equivVanish_conj_complex_dual
alias complex_valued_neat_complex_dual := equivVanish_neat_complex_dual
alias complex_valued_neatConj_complex_dual := equivVanish_neatConj_complex_dual
alias complex_valued_neatSL_complex_dual := equivVanish_neatSL_complex_dual
alias complex_valued_gammaN_complex_dual := equivVanish_gammaN_complex_dual
alias complex_valued_K_complex_dual := equivVanish_K_complex_dual
alias complex_valued_kSL_complex_dual := equivVanish_kSL_complex_dual
alias complex_valued_GL_complex_dual := equivVanish_GL_complex_dual
alias complex_valued_principal_lit := equivVanish_principal_lit
alias complex_valued_conj_lit := equivVanish_conj_lit
alias complex_valued_neat_lit := equivVanish_neat_lit
alias complex_valued_neatConj_lit := equivVanish_neatConj_lit
alias complex_valued_neatSL_lit := equivVanish_neatSL_lit
alias complex_valued_gammaN_lit := equivVanish_gammaN_lit
alias complex_valued_K_lit := equivVanish_K_lit
alias complex_valued_kSL_lit := equivVanish_kSL_lit
alias complex_valued_GL_lit := equivVanish_GL_lit
alias smooth_exact_lit := compactExact_lit
alias dual_is_rational_contragredient := fischerEquiv_equivariant
alias covering_lit_d := coveringLit_d

/-! ### General arithmetic groups: finite-cover and coefficient descent -/

alias smooth_exact_induced := compactExact_induced
alias singular_of_primitive := singularVanish_of_primitive
alias singular_real_of_comm := singularVanish_real_of_comm
alias singular_dual_of_comm := singularVanish_dual_of_comm
alias singular_complex_of_comm := singularVanish_complex_of_comm
alias singular_complex_dual_of_comm := singularVanish_complex_dual_of_comm
alias singular_lit_of_comm := singularVanish_lit_of_comm
alias singular_principal_real := singularVanish_principal_real
alias singular_principal_dual := singularVanish_principal_dual
alias singular_principal_complex := singularVanish_principal_complex
alias singular_principal_complex_dual := singularVanish_principal_complex_dual
alias singular_principal_lit := singularVanish_principal_lit
alias singular_conj_real := singularVanish_conj_real
alias singular_conj_dual := singularVanish_conj_dual
alias singular_conj_complex := singularVanish_conj_complex
alias singular_conj_complex_dual := singularVanish_conj_complex_dual
alias singular_conj_lit := singularVanish_conj_lit

alias neat_torsionFree := IsNeat.torsionFree
alias singular_neat_real := singularVanish_neat_real
alias singular_neat_dual := singularVanish_neat_dual
alias singular_neat_complex := singularVanish_neat_complex
alias singular_neat_complex_dual := singularVanish_neat_complex_dual
alias singular_neat_lit := singularVanish_neat_lit
alias singular_neatConj_real := singularVanish_neatConj_real
alias singular_neatConj_dual := singularVanish_neatConj_dual
alias singular_neatConj_complex := singularVanish_neatConj_complex
alias singular_neatConj_complex_dual := singularVanish_neatConj_complex_dual
alias singular_neatConj_lit := singularVanish_neatConj_lit
alias singular_neatSL_real := singularVanish_neatSL_real
alias singular_neatSL_dual := singularVanish_neatSL_dual
alias singular_neatSL_complex := singularVanish_neatSL_complex
alias singular_neatSL_complex_dual := singularVanish_neatSL_complex_dual
alias singular_neatSL_lit := singularVanish_neatSL_lit
alias singular_gammaN_real := singularVanish_gammaN_real
alias singular_gammaN_dual := singularVanish_gammaN_dual
alias singular_gammaN_complex := singularVanish_gammaN_complex
alias singular_gammaN_complex_dual := singularVanish_gammaN_complex_dual
alias singular_gammaN_lit := singularVanish_gammaN_lit

alias dual_metric_frame := coordinateCoefficientBilin_iotaC_frame
alias dual_is_contragredient := toDual_rhoC_theta
alias dual_norm_metric := dualNorm_metric_frame
alias lit_norm_metric := litCoeff_normSq_frame
alias lit_equivariant := litPhi_equivariant

end TernaryPeriodPolynomials.Argument.Statements.GeneralCoercivity
