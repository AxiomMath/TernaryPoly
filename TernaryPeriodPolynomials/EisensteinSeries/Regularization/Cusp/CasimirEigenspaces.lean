module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.CasimirCovariance

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

def cuspWeakCasimirEigenspace (cusp : CuspidalRepresentation) (eigenvalue : ℝ) : Submodule ℂ cusp.H where
  carrier := {vector | ∀ test : cusp.smooth,
    inner ℂ vector ((cuspCasimirOperator cusp test).val - (eigenvalue : ℂ) • test.val) = 0}
  zero_mem' := by intro test; simp only [inner_zero_left]
  add_mem' {first second} first_member second_member := by
    intro test
    rw [inner_add_left, first_member test, second_member test, add_zero]
  smul_mem' scalar vector member := by
    intro test
    rw [inner_smul_left, member test, mul_zero]

theorem cuspWeakCasimirEigenspace_isClosed (cusp : CuspidalRepresentation) (eigenvalue : ℝ) :
    IsClosed (cuspWeakCasimirEigenspace cusp eigenvalue : Set cusp.H) := by
  have equality : (cuspWeakCasimirEigenspace cusp eigenvalue : Set cusp.H) =
      ⋂ test : cusp.smooth,
        {vector | inner ℂ vector ((cuspCasimirOperator cusp test).val - (eigenvalue : ℂ) • test.val) = 0} := by
    ext vector
    simp only [Set.mem_iInter]
    rfl
  rw [equality]
  exact isClosed_iInter (fun _ => isClosed_eq (continuous_id.inner continuous_const) continuous_const)

theorem cuspWeakCasimirEigenspace_stable (cusp : CuspidalRepresentation) (eigenvalue : ℝ)
    (matrix : BinaryAdelicGL) {vector : cusp.H}
    (member : vector ∈ cuspWeakCasimirEigenspace cusp eigenvalue) :
    cusp.π matrix vector ∈ cuspWeakCasimirEigenspace cusp eigenvalue := by
  intro test
  let backward := cuspSmoothAction cusp matrix⁻¹ test
  have cancel : cuspSmoothAction cusp matrix backward = test := by
    dsimp only [backward]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have translated :
      cusp.π matrix ((cuspCasimirOperator cusp backward).val - (eigenvalue : ℂ) • backward.val) =
        (cuspCasimirOperator cusp test).val - (eigenvalue : ℂ) • test.val := by
    have equality : cuspSmoothAction cusp matrix
        (cuspCasimirOperator cusp backward - (eigenvalue : ℂ) • backward) =
          cuspCasimirOperator cusp test - (eigenvalue : ℂ) • test := by
      rw [map_sub, map_smul, ← cuspCasimir_covariance, cancel]
    exact congrArg Subtype.val equality
  rw [← translated]
  exact ((cuspUnitaryAction cusp matrix).inner_map_map vector
    ((cuspCasimirOperator cusp backward).val - (eigenvalue : ℂ) • backward.val)).trans (member backward)

theorem cuspCasimir_eigenvector_mem_weak (cusp : CuspidalRepresentation) (eigenvalue : ℝ)
    (vector : cusp.smooth) (eigenvector : cuspCasimirOperator cusp vector = (eigenvalue : ℂ) • vector) :
    vector.val ∈ cuspWeakCasimirEigenspace cusp eigenvalue := by
  intro test
  rw [inner_sub_right, ← cuspCasimirOperator_symmetric, eigenvector,
    Submodule.coe_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal, sub_self]

theorem cuspCasimir_scalar_of_weak_eigenvector (cusp : CuspidalRepresentation) (eigenvalue : ℝ)
    {vector : cusp.H} (nonzero : vector ≠ 0)
    (member : vector ∈ cuspWeakCasimirEigenspace cusp eigenvalue) :
    cuspCasimirOperator cusp = (eigenvalue : ℂ) • (1 : Module.End ℂ cusp.smooth) := by
  have full : cuspWeakCasimirEigenspace cusp eigenvalue = ⊤ := by
    rcases cusp.irreducible (cuspWeakCasimirEigenspace cusp eigenvalue)
      (cuspWeakCasimirEigenspace_isClosed cusp eigenvalue)
      (fun matrix _ member => cuspWeakCasimirEigenspace_stable cusp eigenvalue matrix member) with zero | full
    · rw [zero, Submodule.mem_bot] at member
      exact False.elim (nonzero member)
    · exact full
  apply LinearMap.ext
  intro test
  apply Subtype.ext
  change (cuspCasimirOperator cusp test).val = (eigenvalue : ℂ) • test.val
  have error_member : (cuspCasimirOperator cusp test).val - (eigenvalue : ℂ) • test.val ∈
      cuspWeakCasimirEigenspace cusp eigenvalue := by rw [full]; trivial
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (error_member test))

theorem cuspCasimir_scalar_of_eigenvector (cusp : CuspidalRepresentation) (eigenvalue : ℝ)
    {vector : cusp.smooth} (nonzero : vector ≠ 0)
    (eigenvector : cuspCasimirOperator cusp vector = (eigenvalue : ℂ) • vector) :
    cuspCasimirOperator cusp = (eigenvalue : ℂ) • (1 : Module.End ℂ cusp.smooth) := by
  apply cuspCasimir_scalar_of_weak_eigenvector cusp eigenvalue
    (vector := vector.val) (fun zero => nonzero (Subtype.ext zero))
  exact cuspCasimir_eigenvector_mem_weak cusp eigenvalue vector eigenvector

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
