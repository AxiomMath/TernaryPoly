module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.InfinitesimalOperators
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.PartialSmoothDerivatives

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binary_atInfinity_mul (first second : BinaryRealGL) :
    atInfinity (first * second) = atInfinity first * atInfinity second := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [atInfinity, combineGL, pairMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem cusp_realOrbit_product_contDiffOn (cusp : CuspidalRepresentation)
    (vector : cusp.smooth) :
    ContDiffOn ℝ ⊤
      (fun input : (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) ×
          (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) =>
        cusp.π (atInfinity (invertibleMatrix (input.1 0)))
          (cusp.π (atInfinity (invertibleMatrix (input.2 0))) vector.val))
      ({entries | ∀ index, (entries index).det ≠ 0} ×ˢ
        {entries | ∀ index, (entries index).det ≠ 0}) := by
  let productEntries (input : (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) ×
      (Fin 1 → Matrix (Fin 2) (Fin 2) ℝ)) : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ :=
    fun _ => input.1 0 * input.2 0
  have product_smooth : ContDiff ℝ ⊤ productEntries := by
    apply contDiff_pi.mpr
    intro index
    apply contDiff_pi.mpr
    intro row
    apply contDiff_pi.mpr
    intro column
    simp only [productEntries, Matrix.mul_apply, Fin.sum_univ_two]
    fun_prop
  have product_value (input)
      (member : input ∈ ({entries : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ |
          ∀ index, (entries index).det ≠ 0} ×ˢ
        {entries | ∀ index, (entries index).det ≠ 0})) :
      productEntries input 0 =
        (invertibleMatrix (input.1 0) * invertibleMatrix (input.2 0)).val := by
    simp only [productEntries, Units.val_mul, invertibleMatrix, dite_eq_left (member.1 0),
      dite_eq_left (member.2 0), GeneralLinearGroup.val_mkOfDetNeZero]
  have product_maps : Set.MapsTo productEntries
      ({entries | ∀ index, (entries index).det ≠ 0} ×ˢ
        {entries | ∀ index, (entries index).det ≠ 0})
      {entries | ∀ index, (entries index).det ≠ 0} := by
    intro input member index
    change (productEntries input 0).det ≠ 0
    rw [product_value input member]
    exact (invertibleMatrix (input.1 0) * invertibleMatrix (input.2 0)).det_ne_zero
  apply ((((cusp.smooth_exact vector.val).mp vector.property).1).comp
    product_smooth.contDiffOn product_maps).congr
  intro input member
  change cusp.π _ (cusp.π _ vector.val) =
    cusp.π (atInfinity (invertibleMatrix (productEntries input 0))) vector.val
  rw [product_value input member, invertibleMatrix_val, binary_atInfinity_mul,
    map_mul, Module.End.mul_apply]

theorem cuspInfinitesimalAction_left_translate_fderiv (cusp : CuspidalRepresentation)
    (direction : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) (vector : cusp.smooth)
    (matrix : BinaryRealGL) :
    fderiv ℝ (fun entries : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
      cusp.π (atInfinity matrix)
        (cusp.π (atInfinity (invertibleMatrix (entries 0))) vector.val)) (fun _ => 1) direction =
      cusp.π (atInfinity matrix) (cuspInfinitesimalAction cusp direction vector) := by
  have original_smooth := smooth_contDiffAt_matrix
    (((cusp.smooth_exact vector.val).mp vector.property).1) (fun _ => 1)
  have differentiated :=
    (cuspRealUnitaryAction cusp (atInfinity matrix)).toContinuousLinearMap.hasFDerivAt.comp
      (fun _ : Fin 1 => (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (original_smooth.differentiableAt (by simp)).hasFDerivAt
  have derivative_eq := congrArg (fun linear => linear direction) differentiated.fderiv
  change fderiv ℝ (fun entries : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
      cusp.π (atInfinity matrix)
        (cusp.π (atInfinity (invertibleMatrix (entries 0))) vector.val)) (fun _ => 1) direction =
    cusp.π (atInfinity matrix)
      (fderiv ℝ (fun entries : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
        cusp.π (atInfinity (invertibleMatrix (entries 0))) vector.val) (fun _ => 1) direction)
    at derivative_eq
  simpa only [cuspInfinitesimalAction, cuspOrbitDerivative, LinearMap.coe_mk, AddHom.coe_mk,
    iteratedFDeriv_one_apply, Units.val_one] using derivative_eq

theorem cuspInfinitesimalAction_realOrbit_smooth (cusp : CuspidalRepresentation)
    (direction : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) (vector : cusp.smooth) :
    Smooth (fun realElements : Fin 1 → BinaryRealGL =>
      cusp.π (atInfinity (realElements 0)) (cuspInfinitesimalAction cusp direction vector)) := by
  have commutes := cuspInfinitesimalAction_left_translate_fderiv cusp direction vector
  intro entries member
  have product_smooth := (cusp_realOrbit_product_contDiffOn cusp vector).contDiffAt
    (((invertibleMatrixTuples_isOpen 2 1).prod (invertibleMatrixTuples_isOpen 2 1)).mem_nhds
      (show (entries, fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∈
          ({entries | ∀ index, (entries index).det ≠ 0} ×ˢ
            {entries | ∀ index, (entries index).det ≠ 0}) from
        ⟨member, fun _ => by simp⟩))
  have derivative_smooth : ContDiffAt ℝ ⊤
      (fun first : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
        fderiv ℝ (fun second : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ =>
          cusp.π (atInfinity (invertibleMatrix (first 0)))
            (cusp.π (atInfinity (invertibleMatrix (second 0))) vector.val)) (fun _ => 1))
      entries := by
    apply ContDiffAt.fderiv (n := ⊤)
      (f := fun (first second : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) =>
        cusp.π (atInfinity (invertibleMatrix (first 0)))
          (cusp.π (atInfinity (invertibleMatrix (second 0))) vector.val))
      (g := fun _ => fun _ => (1 : Matrix (Fin 2) (Fin 2) ℝ))
    · exact product_smooth
    · exact contDiffAt_const
    · exact le_top
  have evaluated := derivative_smooth.clm_apply
    (contDiffAt_const (c := direction))
  apply (evaluated.congr_of_eventuallyEq ?_).contDiffWithinAt
  exact Filter.Eventually.of_forall (fun nearby =>
    (commutes (invertibleMatrix (nearby 0))).symm)

theorem cuspInfinitesimalAction_mem_smooth (cusp : CuspidalRepresentation)
    (direction : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) (vector : cusp.smooth) :
    cuspInfinitesimalAction cusp direction vector ∈ cusp.smooth := by
  apply (cusp.smooth_exact _).mpr
  refine ⟨cuspInfinitesimalAction_realOrbit_smooth cusp direction vector, ?_⟩
  obtain ⟨level, level_open, level_compact, fixed⟩ :=
    (((cusp.smooth_exact vector.val).mp vector.property).2)
  refine ⟨level, level_open, level_compact, ?_⟩
  intro binary
  exact cuspOrbitDerivative_mem_finiteFixed cusp level 1
    ⟨vector, fixed⟩ (fun _ => direction) binary

noncomputable def cuspSmoothInfinitesimalAction (cusp : CuspidalRepresentation)
    (direction : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) : Module.End ℂ cusp.smooth :=
  (cuspInfinitesimalAction cusp direction).codRestrict cusp.smooth
    (cuspInfinitesimalAction_mem_smooth cusp direction)

theorem cuspSmoothInfinitesimalAction_val (cusp : CuspidalRepresentation)
    (direction : Fin 1 → Matrix (Fin 2) (Fin 2) ℝ) (vector : cusp.smooth) :
    (cuspSmoothInfinitesimalAction cusp direction vector).val =
      cuspInfinitesimalAction cusp direction vector := rfl

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
