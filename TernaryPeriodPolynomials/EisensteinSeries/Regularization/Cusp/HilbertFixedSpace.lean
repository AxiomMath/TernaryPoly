module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.PrincipalLevel
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.SmoothSeminorms

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def cuspUnitaryAction (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL) :
    cusp.H →ₗᵢ[ℂ] cusp.H where
  toLinearMap := cusp.π matrix
  norm_map' := cusp.unitary matrix

noncomputable def cuspRealUnitaryAction (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL) :
    cusp.H →ₗᵢ[ℝ] cusp.H where
  toLinearMap := (cusp.π matrix).restrictScalars ℝ
  norm_map' := cusp.unitary matrix

theorem cusp_action_joint_continuous (cusp : CuspidalRepresentation) :
    Continuous (fun input : BinaryAdelicGL × cusp.H => cusp.π input.1 input.2) :=
  continuous_prod_of_continuous_lipschitzWith' _ 1
    (fun matrix => (cuspUnitaryAction cusp matrix).lipschitzWith) cusp.continuous

theorem binary_atInfinity_atFinite_commute (realMatrix : BinaryRealGL) (finiteMatrix : BinaryFiniteGL) :
    atInfinity realMatrix * atFinite finiteMatrix = atFinite finiteMatrix * atInfinity realMatrix := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [atInfinity, atFinite, combineGL, pairMatrix, Matrix.mul_apply, Fin.sum_univ_two]

def cuspHilbertFiniteFixedSubmodule (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) :
    Submodule ℂ cusp.H where
  carrier := {vector | ∀ binary : level, cusp.π (atFinite binary.val) vector = vector}
  zero_mem' := by intro binary; exact map_zero _
  add_mem' {first second} first_fixed second_fixed := by
    intro binary
    rw [map_add, first_fixed, second_fixed]
  smul_mem' scalar vector fixed := by
    intro binary
    rw [map_smul, fixed]

theorem cuspHilbertFiniteFixedSubmodule_isClosed (cusp : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) : IsClosed (cuspHilbertFiniteFixedSubmodule cusp level : Set cusp.H) := by
  have equality : (cuspHilbertFiniteFixedSubmodule cusp level : Set cusp.H) =
      ⋂ binary : level, {vector | cusp.π (atFinite binary.val) vector = vector} := by
    ext vector
    simp only [Set.mem_iInter]
    rfl
  rw [equality]
  exact isClosed_iInter (fun binary => isClosed_eq
    (cuspUnitaryAction cusp (atFinite binary.val)).continuous continuous_id)

theorem cuspHilbertFiniteFixedSubmodule_completeSpace (cusp : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) : CompleteSpace (cuspHilbertFiniteFixedSubmodule cusp level) :=
  (cuspHilbertFiniteFixedSubmodule_isClosed cusp level).isComplete.completeSpace_coe

theorem cuspFiniteFixedSubmodule_eq_comap (cusp : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) :
    cuspFiniteFixedSubmodule cusp level =
      (cuspHilbertFiniteFixedSubmodule cusp level).comap cusp.smooth.subtype := rfl

theorem cuspHilbertFiniteFixedSubmodule_real_stable (cusp : CuspidalRepresentation)
    (level : Subgroup BinaryFiniteGL) (realMatrix : BinaryRealGL) {vector : cusp.H}
    (fixed : vector ∈ cuspHilbertFiniteFixedSubmodule cusp level) :
    cusp.π (atInfinity realMatrix) vector ∈ cuspHilbertFiniteFixedSubmodule cusp level := by
  intro binary
  rw [← Module.End.mul_apply, ← map_mul, ← binary_atInfinity_atFinite_commute,
    map_mul, Module.End.mul_apply, fixed binary]

theorem cuspOrbitDerivative_finite_translate (cusp : CuspidalRepresentation) (order : ℕ)
    (vector : cusp.smooth) (finiteMatrix : BinaryFiniteGL) :
    cuspOrbitDerivative cusp order
      ⟨cusp.π (atFinite finiteMatrix) vector.val, cusp.smooth_stable _ _ vector.property⟩ =
      (cuspRealUnitaryAction cusp (atFinite finiteMatrix)).toContinuousLinearMap.compContinuousMultilinearMap
        (cuspOrbitDerivative cusp order vector) := by
  have smooth := smooth_contDiffAt_matrix
    (((cusp.smooth_exact vector.val).mp vector.property).1) (fun _ => 1)
  have derivative := (cuspRealUnitaryAction cusp (atFinite finiteMatrix)).toContinuousLinearMap.iteratedFDeriv_comp_left
    smooth (show (order : WithTop ℕ∞) ≤ ⊤ from le_top)
  have commute : (fun entries : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
      cusp.π (atInfinity (invertibleMatrix (entries 0))) (cusp.π (atFinite finiteMatrix) vector.val)) =
      (fun entries : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
        cusp.π (atFinite finiteMatrix) (cusp.π (atInfinity (invertibleMatrix (entries 0))) vector.val)) := by
    funext entries
    rw [← Module.End.mul_apply, ← map_mul, binary_atInfinity_atFinite_commute,
      map_mul, Module.End.mul_apply]
  change iteratedFDeriv ℝ order _ (fun _ => 1) = _
  rw [commute]
  simpa [Function.comp_def, cuspRealUnitaryAction, cuspOrbitDerivative] using derivative

theorem cuspSmoothSeminorm_finite_translate (cusp : CuspidalRepresentation) (order : ℕ)
    (vector : cusp.smooth) (finiteMatrix : BinaryFiniteGL) :
    cuspSmoothSeminorm cusp order
      ⟨cusp.π (atFinite finiteMatrix) vector.val, cusp.smooth_stable _ _ vector.property⟩ =
      cuspSmoothSeminorm cusp order vector := by
  rw [cuspSmoothSeminorm_apply, cuspOrbitDerivative_finite_translate,
    LinearIsometry.norm_compContinuousMultilinearMap, cuspSmoothSeminorm_apply]

theorem cuspOrbitDerivative_mem_finiteFixed (cusp : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (order : ℕ) (vector : cuspFiniteFixedSubmodule cusp level)
    (directions : Fin order → Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) :
    cuspOrbitDerivative cusp order vector.val directions ∈ cuspHilbertFiniteFixedSubmodule cusp level := by
  intro binary
  have translated : (⟨cusp.π (atFinite binary.val) vector.val.val,
      cusp.smooth_stable _ _ vector.val.property⟩ : cusp.smooth) = vector.val :=
    Subtype.ext (vector.property binary)
  have derivative := cuspOrbitDerivative_finite_translate cusp order vector.val binary.val
  rw [translated] at derivative
  exact (congrArg (fun form => form directions) derivative).symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
