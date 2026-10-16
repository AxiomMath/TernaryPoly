module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SmoothDerivatives
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.Realization
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def cuspOrbitDerivative (cusp : CuspidalRepresentation) (order : ℕ) :
    cusp.smooth →ₗ[ℂ]
      ContinuousMultilinearMap ℝ
        (fun _ : Fin order => Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) cusp.H where
  toFun vector := iteratedFDeriv ℝ order
    (fun entries : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
      cusp.π (atInfinity (invertibleMatrix (entries 0))) vector.val) (fun _ => 1)
  map_add' first second := by
    have first_smooth := smooth_contDiffAt_matrix
      (((cusp.smooth_exact first.val).mp first.property).1) (fun _ => 1)
    have second_smooth := smooth_contDiffAt_matrix
      (((cusp.smooth_exact second.val).mp second.property).1) (fun _ => 1)
    simpa only [Submodule.coe_add, map_add, Units.val_one] using
      fun_iteratedFDeriv_add_apply (first_smooth.of_le le_top) (second_smooth.of_le le_top)
  map_smul' scalar vector := by
    have smooth := smooth_contDiffAt_matrix
      (((cusp.smooth_exact vector.val).mp vector.property).1) (fun _ => 1)
    simpa only [Submodule.coe_smul, map_smul, RingHom.id_apply, Units.val_one] using
      (iteratedFDeriv_const_smul_apply' (a := scalar) (smooth.of_le (show (order : WithTop ℕ∞) ≤ ⊤ from le_top)))

noncomputable def cuspSmoothSeminorm (cusp : CuspidalRepresentation) (order : ℕ) :
    Seminorm ℂ cusp.smooth :=
  (normSeminorm ℂ _).comp (cuspOrbitDerivative cusp order)

theorem cuspSmoothSeminorm_apply (cusp : CuspidalRepresentation) (order : ℕ)
    (vector : cusp.smooth) :
    cuspSmoothSeminorm cusp order vector = ‖cuspOrbitDerivative cusp order vector‖ := rfl

theorem cuspSmoothSeminorm_zero (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    cuspSmoothSeminorm cusp 0 vector = ‖vector.val‖ := by
  rw [cuspSmoothSeminorm_apply]
  change ‖iteratedFDeriv ℝ 0
    (fun entries : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
      cusp.π (atInfinity (invertibleMatrix (entries 0))) vector.val) (fun _ => 1)‖ = _
  rw [norm_iteratedFDeriv_zero]
  exact cusp.unitary _ _

theorem cuspOrbitDerivative_finiteDimensional_continuous (cusp : CuspidalRepresentation)
    (order : ℕ) (subspace : Submodule ℂ cusp.smooth) [FiniteDimensional ℂ subspace] :
    Continuous (fun vector : subspace => cuspOrbitDerivative cusp order vector.val) :=
  ((cuspOrbitDerivative cusp order).comp subspace.subtype).continuous_of_finiteDimensional

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
