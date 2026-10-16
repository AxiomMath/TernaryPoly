module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.DerivedLieAction
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cohomological.Center

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cusp_center_action_smooth (cusp : CuspidalRepresentation) (idele : Adelesˣ) (vector : cusp.smooth) :
    cusp.π (GeneralLinearGroup.scalar (Fin 2) idele) vector.val =
      cusp.centralCharacter idele • vector.val := by
  have equality : (⟨cusp.π (GeneralLinearGroup.scalar (Fin 2) idele) vector.val,
      cusp.smooth_stable _ _ vector.property⟩ : cusp.smooth) = cusp.centralCharacter idele • vector := by
    apply cusp.injective
    funext argument
    rw [cusp.equivariant, ← GeneralLinearGroup.scalar_commute,
      cusp.central, map_smul, Pi.smul_apply, smul_eq_mul]
  exact congrArg Subtype.val equality

theorem cohomological_center_action {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (idele : Adelesˣ) (vector : cusp.H) :
    cusp.π (GeneralLinearGroup.scalar (Fin 2) idele) vector = cusp.centralCharacter idele • vector := by
  have closed : IsClosed {vector : cusp.H |
      cusp.π (GeneralLinearGroup.scalar (Fin 2) idele) vector = cusp.centralCharacter idele • vector} :=
    isClosed_eq (cuspUnitaryAction cusp _).continuous (continuous_const.smul continuous_id)
  exact closure_minimal (fun vector member => cusp_center_action_smooth cusp idele ⟨vector, member⟩)
    closed ((cohomological_smooth_dense cohomological) vector)

theorem cohomological_positive_scalar_action {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (scalar : ℝˣ) (positive : 0 < scalar.val)
    (vector : cusp.H) :
    cusp.π (atInfinity (GeneralLinearGroup.scalar (Fin 2) scalar)) vector = vector := by
  rw [atInfinity_scalar, cohomological_center_action cohomological,
    cohomological_centralCharacter_positive cohomological scalar positive, one_smul]

theorem cohomological_derived_identity_zero {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) : cuspDerivedAction cusp 1 = 0 := by
  apply LinearMap.ext
  intro vector
  apply Subtype.ext
  rw [cuspDerivedAction_apply_val]
  have smooth : ContDiffAt ℝ ⊤ (cuspMatrixOrbit cusp vector) (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
    cuspMatrixOrbit_contDiffAt cusp vector 1
  have curve_derivative : HasDerivAt
      (fun scalar : ℝ => scalar • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 1 1 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (1 : ℝ)).smul_const (1 : Matrix (Fin 2) (Fin 2) ℝ)
  have orbit_derivative := (smooth.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    1 curve_derivative (by simp)
  have near : (fun scalar : ℝ => cuspMatrixOrbit cusp vector (scalar • 1)) =ᶠ[nhds 1]
      (fun _ => vector.val) := by
    have positive_near : ∀ᶠ scalar : ℝ in nhds 1, 0 < scalar :=
      (isOpen_lt continuous_const continuous_id).eventually_mem (by norm_num)
    filter_upwards [positive_near] with scalar positive
    let unit : ℝˣ := Units.mk0 scalar positive.ne'
    have value : (GeneralLinearGroup.scalar (Fin 2) unit).val = scalar • 1 := by
      apply Matrix.ext
      intro row column
      fin_cases row <;> fin_cases column <;> simp [unit, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    rw [← value, cuspMatrixOrbit, invertibleMatrix_val]
    exact cohomological_positive_scalar_action cohomological unit positive vector.val
  have constant_derivative := (hasDerivAt_const (1 : ℝ) vector.val).congr_of_eventuallyEq near
  have equality := orbit_derivative.unique constant_derivative
  simpa only [one_smul, LinearMap.zero_apply, Submodule.coe_zero] using equality

theorem cohomological_derived_scalar_zero {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (scalar : ℝ) :
    cuspDerivedAction cusp (scalar • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0 := by
  rw [map_smul, cohomological_derived_identity_zero cohomological, smul_zero]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
