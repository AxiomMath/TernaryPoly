module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.HilbertPair
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.CasimirEigenspaces

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

def cuspWeakCasimirGraph (cusp : CuspidalRepresentation) : Submodule ℂ (WithLp 2 (cusp.H × cusp.H)) where
  carrier := {pair | ∀ test : cusp.smooth,
    inner ℂ pair.ofLp.2 test.val = inner ℂ pair.ofLp.1 (cuspCasimirOperator cusp test).val}
  zero_mem' := by
    intro test
    change inner ℂ (0 : cusp.H) test.val = inner ℂ (0 : cusp.H) (cuspCasimirOperator cusp test).val
    simp only [inner_zero_left]
  add_mem' {first second} first_member second_member := by
    intro test
    change inner ℂ (first.ofLp.2 + second.ofLp.2) test.val =
      inner ℂ (first.ofLp.1 + second.ofLp.1) (cuspCasimirOperator cusp test).val
    rw [inner_add_left, inner_add_left, first_member test, second_member test]
  smul_mem' scalar pair member := by
    intro test
    change inner ℂ (scalar • pair.ofLp.2) test.val =
      inner ℂ (scalar • pair.ofLp.1) (cuspCasimirOperator cusp test).val
    rw [inner_smul_left, inner_smul_left, member test]

theorem cuspWeakCasimirGraph_isClosed (cusp : CuspidalRepresentation) :
    IsClosed (cuspWeakCasimirGraph cusp : Set (WithLp 2 (cusp.H × cusp.H))) := by
  have equality : (cuspWeakCasimirGraph cusp : Set (WithLp 2 (cusp.H × cusp.H))) =
      ⋂ test : cusp.smooth, {pair | inner ℂ (cuspPairSecond cusp pair) test.val =
        inner ℂ (cuspPairFirst cusp pair) (cuspCasimirOperator cusp test).val} := by
    ext pair
    simp only [Set.mem_iInter]
    rfl
  rw [equality]
  exact isClosed_iInter (fun _ => isClosed_eq
    ((cuspPairSecond cusp).continuous.inner continuous_const)
    ((cuspPairFirst cusp).continuous.inner continuous_const))

instance cuspWeakCasimirGraph_completeSpace (cusp : CuspidalRepresentation) :
    CompleteSpace (cuspWeakCasimirGraph cusp) :=
  (cuspWeakCasimirGraph_isClosed cusp).isComplete.completeSpace_coe

theorem cuspWeakCasimirGraph_contains (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    WithLp.toLp 2 (vector.val, (cuspCasimirOperator cusp vector).val) ∈ cuspWeakCasimirGraph cusp := by
  intro test
  exact cuspCasimirOperator_symmetric cusp vector test

theorem cuspWeakCasimirGraph_vertical_zero {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) {pair : WithLp 2 (cusp.H × cusp.H)}
    (member : pair ∈ cuspWeakCasimirGraph cusp) (first_zero : pair.ofLp.1 = 0) : pair = 0 := by
  have second_zero : pair.ofLp.2 = 0 := by
    apply cohomological_inner_ext cohomological
    intro test
    rw [member test, first_zero, inner_zero_left]
  apply WithLp.ofLp_injective
  exact Prod.ext first_zero second_zero

theorem cuspWeakCasimirGraph_stable (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL)
    {pair : WithLp 2 (cusp.H × cusp.H)} (member : pair ∈ cuspWeakCasimirGraph cusp) :
    cuspPairAction cusp matrix pair ∈ cuspWeakCasimirGraph cusp := by
  intro test
  let backward := cuspSmoothAction cusp matrix⁻¹ test
  have cancel : cuspSmoothAction cusp matrix backward = test := by
    dsimp only [backward]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have first_cancel : cusp.π matrix backward.val = test.val := congrArg Subtype.val cancel
  have second_cancel : cusp.π matrix (cuspCasimirOperator cusp backward).val =
      (cuspCasimirOperator cusp test).val := by
    have equality := cuspCasimir_covariance cusp matrix backward
    rw [cancel] at equality
    exact (congrArg Subtype.val equality).symm
  change inner ℂ (cusp.π matrix pair.ofLp.2) test.val =
    inner ℂ (cusp.π matrix pair.ofLp.1) (cuspCasimirOperator cusp test).val
  rw [← first_cancel, ← second_cancel]
  exact ((cuspUnitaryAction cusp matrix).inner_map_map _ _).trans
    ((member backward).trans ((cuspUnitaryAction cusp matrix).inner_map_map _ _).symm)

theorem cuspWeakCasimirGraph_projection_covariance (cusp : CuspidalRepresentation)
    (matrix : BinaryAdelicGL) (pair : WithLp 2 (cusp.H × cusp.H)) :
    (cuspWeakCasimirGraph cusp).starProjection (cuspPairAction cusp matrix pair) =
      cuspPairAction cusp matrix ((cuspWeakCasimirGraph cusp).starProjection pair) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact cuspWeakCasimirGraph_stable cusp matrix
      ((cuspWeakCasimirGraph cusp).starProjection_apply_mem pair)
  · intro test member
    have backward_member := cuspWeakCasimirGraph_stable cusp matrix⁻¹ member
    rw [← map_sub]
    conv_lhs => arg 3; rw [← cuspPairAction_inv cusp matrix test]
    rw [cuspPairAction_inner]
    exact Submodule.starProjection_inner_eq_zero pair _ backward_member

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
