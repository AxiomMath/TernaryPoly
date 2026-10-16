module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.SmoothDensity
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.WithLp

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def cuspInfinitesimalAction (cusp : CuspidalRepresentation)
    (direction : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) : cusp.smooth →ₗ[ℂ] cusp.H where
  toFun vector := cuspOrbitDerivative cusp 1 vector (fun _ => direction)
  map_add' first second := by rw [map_add]; rfl
  map_smul' scalar vector := by rw [map_smul]; rfl

theorem cuspInfinitesimalAction_norm_le (cusp : CuspidalRepresentation)
    (direction : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) (vector : cusp.smooth) :
    ‖cuspInfinitesimalAction cusp direction vector‖ ≤
      cuspSmoothSeminorm cusp 1 vector * ‖direction‖ := by
  simpa only [Fin.prod_univ_one, cuspSmoothSeminorm_apply, cuspInfinitesimalAction,
    LinearMap.coe_mk, AddHom.coe_mk] using
    (cuspOrbitDerivative cusp 1 vector).le_opNorm (fun _ => direction)

theorem binary_atInfinity_one : atInfinity (1 : BinaryRealGL) = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;> simp [atInfinity, combineGL, pairMatrix]

theorem cuspInfinitesimalAction_skew (cusp : CuspidalRepresentation)
    (direction : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) (first second : cusp.smooth) :
    inner ℂ (cuspInfinitesimalAction cusp direction first) second.val +
      inner ℂ first.val (cuspInfinitesimalAction cusp direction second) = 0 := by
  have first_smooth := smooth_contDiffAt_matrix
    (((cusp.smooth_exact first.val).mp first.property).1) (fun _ => 1)
  have second_smooth := smooth_contDiffAt_matrix
    (((cusp.smooth_exact second.val).mp second.property).1) (fun _ => 1)
  have constant_inner :
      (fun entries : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
        inner ℂ (cusp.π (atInfinity (invertibleMatrix (entries 0))) first.val)
          (cusp.π (atInfinity (invertibleMatrix (entries 0))) second.val)) =
      fun _ => inner ℂ first.val second.val := by
    funext entries
    exact (cuspUnitaryAction cusp _).inner_map_map _ _
  have differentiated := fderiv_inner_apply ℂ
    (first_smooth.differentiableAt (by simp)) (second_smooth.differentiableAt (by simp)) direction
  rw [constant_inner, fderiv_fun_const] at differentiated
  simp only [Pi.zero_apply, _root_.zero_apply] at differentiated
  have matrix_one : invertibleMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    simpa only [Units.val_one] using invertibleMatrix_val (1 : BinaryRealGL)
  simp only [Units.val_one, matrix_one, binary_atInfinity_one, map_one, Module.End.one_apply]
    at differentiated
  simpa only [cuspInfinitesimalAction, cuspOrbitDerivative, LinearMap.coe_mk, AddHom.coe_mk,
    iteratedFDeriv_one_apply, add_comm] using differentiated.symm

theorem cuspInfinitesimalAction_limit_zero
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (direction : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ)
    {I : Type*} {filter : Filter I} [filter.NeBot] (vectors : I → cusp.smooth) {limit : cusp.H}
    (vectors_limit : Tendsto (fun index => (vectors index).val) filter (nhds 0))
    (derivatives_limit : Tendsto (fun index => cuspInfinitesimalAction cusp direction (vectors index))
      filter (nhds limit)) : limit = 0 := by
  apply cohomological_inner_ext cohomological
  intro test
  have pairing_limit := (derivatives_limit.inner (𝕜 := ℂ)
    (tendsto_const_nhds (x := test.val))).add
    (vectors_limit.inner (𝕜 := ℂ)
      (tendsto_const_nhds (x := cuspInfinitesimalAction cusp direction test)))
  have zero_pairings : (fun index =>
      inner ℂ (cuspInfinitesimalAction cusp direction (vectors index)) test.val +
        inner ℂ (vectors index).val (cuspInfinitesimalAction cusp direction test)) = fun _ => 0 :=
    funext (fun index => cuspInfinitesimalAction_skew cusp direction (vectors index) test)
  change Tendsto (fun index =>
      inner ℂ (cuspInfinitesimalAction cusp direction (vectors index)) test.val +
        inner ℂ (vectors index).val (cuspInfinitesimalAction cusp direction test)) filter
      (nhds (inner ℂ limit test.val + inner ℂ 0 (cuspInfinitesimalAction cusp direction test))) at pairing_limit
  rw [zero_pairings, inner_zero_left, add_zero] at pairing_limit
  exact tendsto_nhds_unique pairing_limit tendsto_const_nhds

theorem cuspInfinitesimalAction_limit_eq
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (direction : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ)
    {I : Type*} {filter : Filter I} [filter.NeBot] (vectors : I → cusp.smooth)
    (vector : cusp.smooth) {limit : cusp.H}
    (vectors_limit : Tendsto (fun index => (vectors index).val) filter (nhds vector.val))
    (derivatives_limit : Tendsto (fun index => cuspInfinitesimalAction cusp direction (vectors index))
      filter (nhds limit)) : limit = cuspInfinitesimalAction cusp direction vector := by
  apply sub_eq_zero.mp
  apply cuspInfinitesimalAction_limit_zero cohomological direction
    (filter := filter) (fun index => vectors index - vector)
  · simpa using vectors_limit.sub (tendsto_const_nhds (x := vector.val))
  · simpa only [map_sub] using derivatives_limit.sub
      (tendsto_const_nhds (x := cuspInfinitesimalAction cusp direction vector))

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
