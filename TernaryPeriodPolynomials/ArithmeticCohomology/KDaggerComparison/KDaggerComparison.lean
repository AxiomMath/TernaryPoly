module

public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Transport
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.Inflation
public import TernaryPeriodPolynomials.ArithmeticCohomology.KDaggerComparison.TQ
public import TernaryPeriodPolynomials.BoundaryComparison.PlaneLineComparison

@[expose] public section


/-!
# The `K†` comparison for Proposition C.5

* `lit_class` (`litAll`): the restriction `H²(K†, E_n) → H²(Γ(N), E_n)` read in Mathlib's `H²` of the literal `Γ(N)` (CMP-1, one direction).
* `phi_plane`, `phi_line`, `phi_plane_at`, `phi_line_at`: the face dictionary from the `K†` stratum classes to the face groups of `Γ(N)` (CMP-2).
* `phi_plane_global_coordinates`, `phi_line_global_coordinates`: naturality, the `Γ(N)` boundary of the stratum coordinates of a global `K†`-cocycle
  is the boundary of its literal class (CMP-3).
* `zero_flags_lit_of_inner`, `phi_plane_mem_range`, `phi_line_mem_range`: `InnerBoundary` gives zero flag restrictions and mixed cuspidal faces (CMP-4, forward).
* `eq_zero_of_phi_plane_eq_zero`, `eq_zero_of_phi_line_eq_zero`: injectivity of the face dictionary (CMP-2).
* `identification`, `graph_clause_of_gamma_n`, `prop_C_5_comparison`: CMP-5 / CMP-C5, `T` is the transport of the printed `Γ(N)` constant term.
* `constant_terms_of_gamma_n`, `zero_flags_lit_iff`, `exists_T_q_gamma_n`: the existence clause by averaging, the converse of CMP-4, and `T := T_Q` (CMP-C5).
* `frozen_prop_C_5_comparison`: the instance at `N = 6` for the `T` of the `line_constant_term_comparison`.
* `constant_terms_from_gamma_six`, `prop_C_5_from_gamma_six`: the `constant_terms` and `line_constant_term_comparison` re-derived from the literal `Γ(6)` Proposition C.5.

Formalized by Claude Sonnet 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.KDaggerComparison

open TernaryPeriodPolynomials.Argument.KDaggerComparison
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.FormClassK
open GeneralEisenstein GeneralEisenstein.Homogeneous

alias lit_class := litAll
alias lit_class_injective := litClass_injective
alias mem_range_lit_class_iff := mem_range_litClass_iff
alias class_principal_lit_class := classPrincipal_litClass
alias phi_plane_at := phiPlaneAt
alias phi_line_at := phiLineAt
alias phi_plane := phiPlane
alias phi_line := phiLine
alias phi_plane_global_coordinates := phiPlane_globalCoordinates
alias phi_line_global_coordinates := phiLine_globalCoordinates
alias zero_flags_lit_of_inner := zeroFlags_litAll_of_inner
alias phi_plane_mem_range := phiPlane_mem_range
alias phi_line_mem_range := phiLine_mem_range
alias eq_zero_of_phi_plane_eq_zero := eq_zero_of_phiPlane_eq_zero
alias eq_zero_of_phi_line_eq_zero := eq_zero_of_phiLine_eq_zero
alias identification_of_class_gamma_n := identification_of_class
alias identification_gamma_n := identification
alias graph_clause_of_gamma_n := graph_clause_of_gammaN
alias line_coordinate_eq_of_plane_eq_gamma_n := line_coordinate_eq_of_plane_eq
alias prop_C_5_comparison_gamma_n := prop_C_5_comparison
alias constant_terms_of_gamma_n := constant_terms_of_gammaN
alias zero_flags_lit_iff := zeroFlags_litAll_iff
alias exists_T_q_gamma_n := exists_TQ

/-- **The `line_constant_term_comparison` is the transport of the literal `Γ(6)` Proposition C.5.**  Let `T` be the map of the `line_constant_term_comparison`.
Then for the printed constant term `TΓ` of `propC5_gammaN_printed` at `N = 6`: `TΓ` has the printed seed property and the `Γ(6)` graph clause,
and for every `InnerBoundary` plane class `ξ` there is `ξ' ∈ 𝒞_P(E)` with `ξ'` the `Γ(6)` plane boundary of `ξ` and `TΓ ξ'` the `Γ(6)` line
boundary of `T ξ`. -/
theorem frozen_prop_C_5_comparison (n : ℕ) (hn : 4 ≤ n) :
    ∃ TΓ : PlaneCuspSum 6 n →ₗ[ℂ] LineCuspSum 6 n,
      (∀ (f : TwTuple 6 n) (ξ : PlaneCuspSum 6 n), planeCuspSumEmbedding 6 n ξ = seedBoundary 6 n f →
        lineCuspSumEmbedding 6 n (TΓ ξ) =
          lineBoundary 6 n (classCG 6 n hn f)) ∧
      GraphMapGamma 6 n TΓ ∧
      ∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
        ∃ ξ' : PlaneCuspSum 6 n, planeCuspSumEmbedding 6 n ξ' = phiPlane 6 (by norm_num) (by norm_num) n ξ ∧
          lineCuspSumEmbedding 6 n (TΓ ξ') =
            phiLine 6 (by norm_num) (by norm_num) n ((line_constant_term_comparison n hn).choose ξ) := by
  obtain ⟨TΓ, h1, hG, h2⟩ := prop_C_5_comparison 6 (by norm_num) (by norm_num) n hn
  refine ⟨TΓ, h1, hG, (h2 _ fun ξ hξ => ?_).2⟩
  exact ((line_constant_term_comparison n hn).choose_spec.1 ξ hξ).2

/-- **The `constant_terms`, from the literal `Γ(6)` Proposition C.5** (same statement as `constant_terms`): every `InnerBoundary`
plane class is the plane coordinate of a global `K†`-cocycle whose line coordinate is `InnerBoundary`. -/
theorem constant_terms_from_gamma_six (n : ℕ) (hn : 4 ≤ n) (ξ : StratumH2 n trivialCharacter .plane)
    (hξ : InnerBoundary n trivialCharacter .plane ξ) :
    ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      (globalCoordinates n trivialCharacter c).1 = ξ ∧
      InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 :=
  constant_terms_of_gammaN (N := 6) (n := n) (by norm_num) (by norm_num) hn ξ hξ

/-- **The `line_constant_term_comparison`, from the literal `Γ(6)` Proposition C.5** (same statement as `line_constant_term_comparison`), with `T` the transport
`T_Q` of the printed `Γ(6)` constant term (`exists_TQ`). -/
theorem prop_C_5_from_gamma_six (n : ℕ) (hn : 4 ≤ n) :
    ∃ T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line,
      (∀ ξ, InnerBoundary n trivialCharacter .plane ξ →
        InnerBoundary n trivialCharacter .line (T ξ) ∧
          ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
            globalCoordinates n trivialCharacter c = (ξ, T ξ)) ∧
      ∀ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        InnerBoundary n trivialCharacter .plane (globalCoordinates n trivialCharacter c).1 →
        InnerBoundary n trivialCharacter .line (globalCoordinates n trivialCharacter c).2 →
        (globalCoordinates n trivialCharacter c).2 = T (globalCoordinates n trivialCharacter c).1 := by
  obtain ⟨TΓ, -, -, T, h1, h2, -⟩ := exists_TQ 6 (by norm_num) (by norm_num) n hn
  exact ⟨T, h1, h2⟩

end TernaryPeriodPolynomials.Argument.Statements.KDaggerComparison
