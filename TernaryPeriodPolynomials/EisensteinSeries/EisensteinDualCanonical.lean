module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.RepMain
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.LinePrinted
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.DualConstantTerms

@[expose] public section


/-!
# Exports: the dual constant terms `r_P ℰ_Q^∨(η) = T^∨η` and the change of face representatives

Formalized by Claude Sonnet 5.5.

What is proved, and under which hypothesis:

* UNCONDITIONAL (`3 ≤ N`, `4 ≤ n`): the plane row of the dual series in printed coordinates (`dual_rP_printed`, `dual_rP_dualClassC`); the complex mirror of the transport of constant terms
  (`dual_constant_terms_T_C`); `T^∨η` and `r_P ℰ^∨` are cuspidal (`dual_rP_mem_dualCuspidalP`, `dualRP_mem_dualCuspidalP`); change of cusp representative for the series
  (`exists_cuspChange_class`) and of the dual class (`dualE_eq_dualEJ`).
* UNCONDITIONAL since the `EichlerShimuraInj.seedMapInjective`: the `*_uncond` versions of the conditional statements below.
* CONDITIONAL (with canonicity of `T` as an explicit hypothesis) (`FormClassK.ClassicalLineConstantTerm N n hn`, which follows from the Eichler-Shimura injectivity `SeedMapInjective`): the existence of ONE linear
  `T^∨` with `r_P ℰ^∨(η) = T^∨ η` (`dual_rP_eq_dualT_of_canonical` for the representatives `ȷ(planeFaceRepr x)`, `dual_rP_eq_dualT_of_canonical_reps` for the `LineFaces.rep`,
  `dual_rP_eq_dualT_of_canonical_literal` for the literal contragredient), `dual_constant_terms_all`, `dual_Td_mem_dualCuspidalP`.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.EisensteinDualCanonical

open TernaryPeriodPolynomials.Argument.EisensteinDual TernaryPeriodPolynomials.Argument.EisensteinClass

-- printed coordinates of the dual plane row
alias dual_plane_row_named := dual_rP_dualClassC
alias dual_plane_row_printed := dual_rP_printed
alias dual_plane_row_conjugation := lineAtHom_comp_jRestr
-- complex mirror
alias face_pullback_complex_bijective := facePullC_bijective
alias dual_constant_terms_transport_complex := dual_constant_terms_transport_C
alias dual_second_constant_term_complex := dualTC
alias dual_constant_terms_complex := dual_constant_terms_T_C
-- the dual series for the ȷ-images of the faces
alias dual_global_class := dualEJ
alias dual_global_class_eq_pullback := dualEJ_eq
alias dual_cuspidal_plane := dualCuspidalP
alias dual_cuspidal_plane_pullback := dualCuspidalP_jmath
alias dual_plane_coordinate_cuspidal := dual_rP_mem_dualCuspidalP
alias dual_seed_vector_exists := dual_seed_exists
-- conditional on canonicity of T
alias dual_plane_row_canonical := dual_rP_eq_dualT_of_canonical
alias dual_constant_terms_canonical := dual_constant_terms_all
alias dual_second_constant_term_cuspidal := dual_Td_mem_dualCuspidalP
-- change of face representatives
alias series_cusp_change := EisensteinClass.exists_cuspChange_class
alias series_cusp_change_full := EisensteinClass.exists_cuspChange_full
alias dual_face_equiv := jFaceEquiv
alias dual_class_rep_change := dualE_eq_dualEJ
alias dual_plane_coordinate_vanishes := dualRP_eq_zero_of_dualS_eq_zero
alias dual_plane_coordinate_cuspidal_reps := dualRP_mem_dualCuspidalP
alias dual_plane_row_canonical_reps := dual_rP_eq_dualT_of_canonical_reps
alias dual_plane_row_canonical_literal := dual_rP_eq_dualT_of_canonical_literal

-- UNCONDITIONAL (canonicity of T from S4's Eichler-Shimura injectivity)
alias canonical_line_constant_term := classicalLineConstantTerm
alias dual_plane_row_reps := dual_rP_eq_dualT_reps
alias dual_plane_row_literal := dual_rP_eq_dualT_literal
alias dual_constant_terms_unconditional := dual_constant_terms_all_uncond
alias dual_second_constant_term_cuspidal_unconditional := dual_Td_mem_dualCuspidalP_uncond
alias dual_plane_row := dual_rP_eq_dualT

end TernaryPeriodPolynomials.Argument.Statements.EisensteinDualCanonical
